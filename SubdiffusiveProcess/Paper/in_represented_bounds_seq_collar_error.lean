module

public import SubdiffusiveProcess.Paper.conv_represented_bounds_env_product
public import SubdiffusiveProcess.Paper.lem_20
public import SubdiffusiveProcess.Paper.prop_locality_recovery

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The exact plateau clause of the represented cutoff forces its native weak gradient to
vanish in the open region beyond the plateau. This is the gradient-zero input required by
`lem_20_collar_energy`; it is not inferred from the arithmetic scale bracket. -/
theorem aux_in_represented_bounds_seq_collar_error_grad_zero
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (chiS : S.space) (chi : SpatialCoordinates d → ℝ) (rho : ℝ)
    (hchi : (chiS.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chi)
    (hone : ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho ≤ Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ → chi x = 1) :
    ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho < Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chiS.val.2 i : SpatialCoordinates d → ℝ) x = 0 := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let U : Set (SpatialCoordinates d) :=
    {x | x ∈ Q ∧ 3 * rho < Metric.infDist x Qᶜ}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (centeredCube z R hR).isOpen.inter
      (isOpen_lt continuous_const (Metric.continuous_infDist_pt _))
  have hconst : ∀ᵐ x ∂volume.restrict Q, x ∈ U → chiS.val.1 x = 1 := by
    filter_upwards [hchi, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
      with x hprofile hxQ hxU
    have hxcl : x ∈ closure Q := subset_closure hxQ
    have honeX := hone x hxcl (le_of_lt hxU.2)
    rw [hprofile]
    exact honeX
  have hweak : chiS.val ∈ weakSobolevGraph (centeredCube z R hR) :=
    killedSobolevGraph_le_weakSobolevGraph (hS ▸ chiS.property)
  intro i
  have hgrad := aux_prop_locality_recovery_grad_ae_zero_of_const
    chiS.val hweak U hUopen 1 hconst i
  filter_upwards [hgrad, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet]
    with x hx hxQ
  intro hxU
  exact hx ⟨hxQ, hxU⟩

/-- Turn the actual product value and Leibniz gradient supplied by `hW` into the data for
the subtraction `u - w` used by the collar-energy estimate. The cutoff's `ResponseSpace`
representative is explicitly identified with its native H¹ representative. -/
theorem aux_in_represented_bounds_seq_collar_error_subtraction
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (u w chiS : S.space) (un : H10Function
      (centeredCube z R hR : Set (SpatialCoordinates d)))
    (v : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (uc profile : SpatialCoordinates d → ℝ)
    (hchiS : chiS.val = sobolevDataOfH1 v)
    (hchiProfile : (chiS.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] profile)
    (huval : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc)
    (hunval : un.toH1Function.toFun
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc)
    (hungrad : ∀ i : Fin d,
      (fun x => un.toH1Function.grad x i)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => (u.val.2 i : SpatialCoordinates d → ℝ) x))
    (hwval : (w.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => uc x * profile x))
    (hwgrad : ∀ i : Fin d,
      (fun x => (w.val.2 i : SpatialCoordinates d → ℝ) x)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => un.toH1Function.toFun x * v.grad x i +
            v.toFun x * un.toH1Function.grad x i)) :
    ((u - w).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        (fun x => uc x * (1 - (chiS.val.1 : SpatialCoordinates d → ℝ) x)) ∧
    ∀ i : Fin d,
      (fun x => ((u - w).val.2 i : SpatialCoordinates d → ℝ) x)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => (1 - (chiS.val.1 : SpatialCoordinates d → ℝ) x) *
            (u.val.2 i : SpatialCoordinates d → ℝ) x -
            uc x * (chiS.val.2 i : SpatialCoordinates d → ℝ) x) := by
  let μ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))
  have hchiVal : (chiS.val.1 : SpatialCoordinates d → ℝ) =ᵐ[μ] v.toFun := by
    rw [hchiS]
    exact sobolevDataOfH1_fst_coeFn v
  have hchiGrad : ∀ i : Fin d,
      (fun x => (chiS.val.2 i : SpatialCoordinates d → ℝ) x)
        =ᵐ[μ] (fun x => v.grad x i) := by
    intro i
    rw [hchiS]
    exact sobolevDataOfH1_snd_coeFn v i
  have hsubvalLP : ((u - w).val.1 : DomainL2 (centeredCube z R hR)) =
      u.val.1 - w.val.1 := by
    change (((u - w : S.space) : SobolevData (centeredCube z R hR)).1) = _
    rw [Submodule.coe_sub]
    rfl
  have hsubval : ((u - w).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[μ] (fun x => (u.val.1 : SpatialCoordinates d → ℝ) x -
        (w.val.1 : SpatialCoordinates d → ℝ) x) := by
    rw [hsubvalLP]
    exact Lp.coeFn_sub u.val.1 w.val.1
  have hsubgradLP : ∀ i : Fin d,
      ((u - w).val.2 i : DomainL2 (centeredCube z R hR)) = u.val.2 i - w.val.2 i := by
    intro i
    change (((u - w : S.space) : SobolevData (centeredCube z R hR)).2 i) = _
    rw [Submodule.coe_sub]
    rfl
  have hsubgrad : ∀ i : Fin d,
      (fun x => ((u - w).val.2 i : SpatialCoordinates d → ℝ) x)
        =ᵐ[μ] (fun x => (u.val.2 i : SpatialCoordinates d → ℝ) x -
          (w.val.2 i : SpatialCoordinates d → ℝ) x) := by
    intro i
    rw [hsubgradLP i]
    exact Lp.coeFn_sub (u.val.2 i) (w.val.2 i)
  constructor
  · filter_upwards [hsubval, huval, hwval, hchiProfile] with x hsub hu hw hprof
    calc
      (u - w).val.1 x = uc x - uc x * profile x := by rw [hsub, hu, hw]
      _ = uc x * (1 - chiS.val.1 x) := by rw [← hprof]; ring
  · intro i
    filter_upwards [hsubgrad i, hunval, hungrad i, hwgrad i, hchiVal, hchiGrad i] with x
      hsub hun hunG hw hv hvg
    calc
      (u - w).val.2 i x =
          u.val.2 i x - (uc x * v.grad x i + v.toFun x * u.val.2 i x) := by
        rw [hsub, hw, hun, hunG]
      _ = (1 - chiS.val.1 x) * u.val.2 i x - uc x * chiS.val.2 i x := by
        rw [← hv, ← hvg]
        ring

/-- All-scale hCollarError reduction using the source's actual all-centres local-energy
growth, Holder representative, the exact cutoff energy supplier, and the actual hW product
gradient. The quantitative cutoff energy is supplied by the joint collar construction. The source
growth estimate is needed only for balls of radius at most one; the resulting collar bound
holds for every positive collar radius. -/
theorem in_represented_bounds_seq_collar_error
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (t alpha eta : ℝ)
    (htLower : (d : ℝ) - 1 < t) (htUpper : t < (d : ℝ))
    (hAlphaLower : 1 / 2 < alpha) (hAlphaUpper : alpha < 1)
    (hEta : 0 < eta) (hEtaAlpha : 1 + eta < 2 * alpha)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (rho : ℕ → ℝ) (hRho : ∀ k, 0 < rho k)
    (KN : ℕ → ℝ) (Kstar : ℝ)
    (hKN : ∀ n, 1 ≤ KN n ∧ KN n ≤ Kstar)
    (u : ℕ → S.space) (uc : ℕ → SpatialCoordinates d → ℝ)
    (hUrep : ∀ n, (u n).val.1
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc n)
    (hcont : ∀ n, ContinuousOn (uc n)
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hboundary : ∀ n x, x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)) →
      uc n x = 0)
    (hholder : ∀ n x y,
      x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      |uc n x - uc n y| ≤ KN n * dist x y ^ alpha)
    (hgrowth : ∀ n x s, 0 < s → s ≤ 1 →
      (((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((a n).val y *
          ∑ i : Fin d, ((u n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x s)).toReal ≤ KN n * s ^ t)
    (chi : ℕ → ℕ → S.space) (w : ℕ → ℕ → S.space)
    (hchiRange : ∀ k n, ∀ᵐ x ∂volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      0 ≤ (chi k n).val.1 x ∧ (chi k n).val.1 x ≤ 1)
    (hchiOne : ∀ k n, ∀ᵐ x ∂volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho k ≤ Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi k n).val.1 x = 1)
    (hchiGrad : ∀ k n (i : Fin d), ∀ᵐ x ∂volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho k < Metric.infDist x
        (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
        (chi k n).val.2 i x = 0)
    (Ccut : ℝ) (hCcut : 0 < Ccut)
    (hchiEnergy : ∀ k n,
      responseForm S (a n) (chi k n) (chi k n) ≤
        Ccut * KN n * rho k ^ (-1 - eta))
    (hprodVal : ∀ k n,
      ((u n - w k n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => (uc n x) * (1 - (chi k n).val.1 x)))
    (hprodGrad : ∀ k n i,
      (fun x => ((u n - w k n).val.2 i : SpatialCoordinates d → ℝ) x)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => (1 - (chi k n).val.1 x) * (u n).val.2 i x -
            uc n x * (chi k n).val.2 i x)) :
    ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k n,
      responseForm S (a n) (u n - w k n) (u n - w k n) ≤
        Kf * (rho k ^ (t - (d : ℝ) + 1) + rho k ^ (2 * alpha - 1 - eta)) := by
  obtain ⟨Cmass, hCmass, hmass⟩ :=
    aux_lem_20_collar_mass_all_radii d hd z R hR t htLower htUpper
  let Ccore : ℝ := max (2 * Cmass) (2 * Ccut * 3 ^ (2 * alpha))
  have hCcore : 0 ≤ Ccore := by
    dsimp [Ccore]
    exact le_max_of_le_left (by positivity)
  have hKstar : 0 ≤ Kstar := by linarith [(hKN 0).1, (hKN 0).2]
  refine ⟨Ccore * Kstar * (1 + Kstar ^ 2), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hCcore hKstar) (by positivity)
  · intro k n
    let r := rho k
    have hr : 0 < r := hRho k
    have hKNn := hKN n
    have hM0 : 0 ≤ KN n * (3 * r) ^ alpha :=
      mul_nonneg (by linarith [hKNn.1]) (Real.rpow_nonneg (by positivity) _)
    have hholder1 : ∀ x y,
        x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
        y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
        |uc n x - uc n y| ≤ KN n * 1 * dist x y ^ alpha := by
      intro x y hx hy
      simpa using hholder n x y hx hy
    have hAmp0 := aux_lem_20_collar_amplitude_all_radii d hd z R hR alpha hAlphaLower hAlphaUpper
      (KN n) 1 hKNn.1 (by norm_num) (uc n) (hcont n) (hboundary n) hholder1
      r hr
    have hAmp : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ 3 * r →
        |uc n x| ≤ KN n * (3 * r) ^ alpha := by
      intro x hx hdist
      simpa using hAmp0 x hx hdist
    have hmassn := hmass S hS (a n) (u n) (KN n) hKNn.1 (hgrowth n) r hr
    have henergy := aux_lem_20_collar_energy_all_radii d hd z R hR S hS (a n) (u n)
      (chi k n) (u n - w k n) (uc n) (hUrep n) (hprodVal k n)
      (hprodGrad k n) r hr (hchiRange k n) (hchiOne k n)
      (hchiGrad k n) (KN n * (3 * r) ^ alpha) hM0 (hAmp)
    have hstep : responseForm S (a n) (u n - w k n) (u n - w k n) ≤
        2 * (Cmass * KN n * r ^ (t - (d : ℝ) + 1)) +
        2 * (KN n * (3 * r) ^ alpha) ^ 2 *
          (Ccut * KN n * r ^ (-1 - eta)) := by
      refine le_trans henergy (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left hmassn (by norm_num)
      · exact mul_le_mul_of_nonneg_left (hchiEnergy k n)
          (mul_nonneg (by norm_num) (sq_nonneg _))
    have hnum := aux_lem20_num Cmass Ccut alpha (t - (d : ℝ) + 1) eta
      (KN n) 1 r (le_of_lt hCmass) (le_of_lt hCcut) hKNn.1
      (by norm_num) hr
    have hnum' : responseForm S (a n) (u n - w k n) (u n - w k n) ≤
        Ccore * KN n * (1 + KN n ^ 2) *
          (r ^ (t - (d : ℝ) + 1) + r ^ (2 * alpha - 1 - eta)) := by
      apply le_trans hstep
      have hrew : 2 * (Cmass * KN n * r ^ (t - (d : ℝ) + 1)) +
          2 * (KN n * (3 * r) ^ alpha) ^ 2 *
            (Ccut * KN n * r ^ (-1 - eta)) =
          2 * (Cmass * KN n * r ^ (t - (d : ℝ) + 1)) +
            2 * (KN n * 1 * (3 * r) ^ alpha) ^ 2 *
              (Ccut * KN n * r ^ (-1 - eta)) := by ring
      rw [hrew]
      simpa [Ccore] using hnum
    have hfactor := aux_lem20_bound Ccore (KN n) 1 Kstar hCcore hKNn.1
      hKNn.2 (by norm_num) hKstar
    have hpow : 0 ≤ r ^ (t - (d : ℝ) + 1) + r ^ (2 * alpha - 1 - eta) :=
      add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _)
    have hfactor' := mul_le_mul_of_nonneg_right hfactor hpow
    exact le_trans hnum' (by nlinarith [hfactor'])

end Paper
