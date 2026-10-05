module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_record_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_deep_grid
public import SubdiffusiveProcess.Paper.lem_as_coarse_deep_record_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_subwavelength
public import SubdiffusiveProcess.Paper.lem_as_coarse_multiscale_assembly
public import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly
public import SubdiffusiveProcess.Paper.lem_as_coarse_record_composition
public import SubdiffusiveProcess.Paper.lem_as_coarse_scalar_cell_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_scalar_consumer
public import SubdiffusiveProcess.Paper.lem_as_coarse_subwave_supplier
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.prop_as_response_bank_shift_invariance
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_cube_geometry
public import SubdiffusiveProcess.Paper.coercivity_dilation
public import Mathlib.Tactic
@[expose] public section

open MeasureTheory Set Filter Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_as_coarse_arith (R C a x b y : ℝ) (h : a * b = 1) :
    R * (C * x * y) = C * R * a * x * (b * y) := by
  calc
    R * (C * x * y) = C * R * x * y := by ring
    _ = C * R * x * y * (a * b) := by rw [h]; ring
    _ = C * R * a * x * (b * y) := by ring

theorem aux_lem_as_coarse_assoc (a b c d : ℝ) :
    (a * b * c) * d = (a * b) * (c * d) := by
  ring

theorem aux_lem_as_coarse_mul
    (x a A K b c : ℝ) (hx : x ≤ a * b * c) (ha : a ≤ A)
    (hA : A ≤ K) (hbc : 0 ≤ b * c) : x ≤ K * b * c := by
  calc
    x ≤ a * (b * c) := by simpa [mul_assoc] using hx
    _ ≤ A * (b * c) := mul_le_mul_of_nonneg_right ha hbc
    _ ≤ K * (b * c) := mul_le_mul_of_nonneg_right hA hbc
    _ = K * b * c := by ring

theorem aux_lem_as_coarse_fractional_dilation
    (d k : ℕ) (hd : 2 ≤ d) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (g : Fin k → DomainL2 (centeredCube z' 1 h1))
    (hfg : ∀ i, ∀ᵐ x ∂volume.restrict
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      g i x = f i (cubeDilation z z' r x)) :
    cubeFractionalVecSqNorm hd z r hr s f ≤
      max 1 (r ^ (-(2 * (s : ℝ)))) *
        cubeFractionalVecSqNorm hd z' 1 h1 s g := by
  have hnorm := _root_.SubdiffusiveProcess.Paper.gagliardo_dilation_scaling d k hd z z' r hr h1 s f g hfg
  have hsemi : cubeFractionalVecSeminormSq hd z r hr s f =
      r ^ (-(2 * (s : ℝ))) * cubeFractionalVecSeminormSq hd z' 1 h1 s g := by
    simp only [cubeFractionalVecSeminormSq]
    rw [← ENNReal.toReal_pow, hnorm.1, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow]
  let R : ℝ := max 1 (r ^ (-(2 * (s : ℝ))))
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold cubeFractionalVecSqNorm
  rw [hsemi, hnorm.2]
  have hsemi0 : 0 ≤ cubeFractionalVecSeminormSq hd z' 1 h1 s g := by
    dsimp [cubeFractionalVecSeminormSq]
    positivity
  have hL20 : 0 ≤ (∑ i : Fin k, ‖g i‖ ^ 2) /
      volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
    positivity
  have hsemi_le : r ^ (-(2 * (s : ℝ))) *
      cubeFractionalVecSeminormSq hd z' 1 h1 s g ≤
      R * cubeFractionalVecSeminormSq hd z' 1 h1 s g :=
    mul_le_mul_of_nonneg_right (le_max_right 1 _) hsemi0
  have hL2_le : (∑ i : Fin k, ‖g i‖ ^ 2) /
      volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) ≤
      R * ((∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
    have hR1 : (1 : ℝ) ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    calc
      _ = 1 * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hR1 hL20
  calc
    r ^ (-(2 * (s : ℝ))) * cubeFractionalVecSeminormSq hd z' 1 h1 s g +
        (∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) ≤
      R * cubeFractionalVecSeminormSq hd z' 1 h1 s g +
        R * ((∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) :=
      add_le_add hsemi_le hL2_le
    _ = R * (cubeFractionalVecSeminormSq hd z' 1 h1 s g +
        (∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by ring
    _ = max 1 (r ^ (-(2 * (s : ℝ)))) *
        (cubeFractionalVecSeminormSq hd z' 1 h1 s g +
          (∑ i : Fin k, ‖g i‖ ^ 2) /
            volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by rfl

theorem aux_lem_as_coarse_coercivity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ Cc : ℝ, 0 < Cc ∧
      (∀ a : PositiveCoefficient (centeredCube z r hr),
        (∀ v : killedSobolevGraph (centeredCube z r hr),
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (v : SobolevData (centeredCube z r hr)).1 ≤
            Cc * (Jc.lam z r hr a z r (1 / 8 : ℝ) 1)⁻¹ *
              sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr))) ∧
        (∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (v : SobolevData (centeredCube z r hr)).1 ≤
            Cc * (Jc.lam z r hr a z r (1 / 8 : ℝ) 1)⁻¹ *
              sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr)))) := by
  have hs8' : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor <;> norm_num
  obtain ⟨Cunit, hCunit, hunit⟩ :=
    _root_.SubdiffusiveProcess.Paper.besov_h34_coercivity d hd Jc Pc Sf (1 / 8 : ℝ) hs8'
  let h1 : (0 : ℝ) < 1 := one_pos
  let R : ℝ := max 1 (r ^ (-(3 / 2 : ℝ)))
  let Cc : ℝ := Cunit * R * r ^ ((2 : ℝ) - (d : ℝ))
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCc : 0 < Cc := by
    dsimp [Cc]
    positivity
  refine ⟨Cc, hCc, ?_⟩
  intro a
  obtain ⟨b, hb⟩ := _root_.SubdiffusiveProcess.Paper.dilation_coefficient_transport d z 0 r hr h1 a
  have hlam : Jc.lam z r hr a z r (1 / 8 : ℝ) 1 =
      Jc.lam (0 : SpatialCoordinates d) 1 h1 b (0 : SpatialCoordinates d) 1
        (1 / 8 : ℝ) 1 := by
    apply Jc.lam_dilation z r hr a 0 h1 b
    filter_upwards [hb] with x hx
    have hxd : cubeDilation z 0 r x = fun i => z i + r * x i := by
      funext i
      simp [cubeDilation]
    simpa [hxd] using hx
  constructor
  · intro v
    obtain ⟨w, hwval, hwgrad⟩ :=
      _root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_killed_pullback d z r hr h1 v
    have hfg : ∀ i : Fin 1, ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (fun _ : Fin 1 => (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) i x =
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) i
            (cubeDilation z 0 r x) := by
      intro i
      simpa using hwval
    have hN := aux_lem_as_coarse_fractional_dilation d 1 hd z 0 r hr h1
      threeQuarterOrder
      (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
      (fun _ : Fin 1 => (w : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) hfg
    have hE := _root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_energy_scaling d z r hr h1 a b
      (v : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) hb hwval hwgrad
    have h0 := (hunit (0 : SpatialCoordinates d) h1 b).1 w |>.2
    have hpow : r ^ ((2 : ℝ) - (d : ℝ)) * r ^ ((d : ℝ) - 2) = 1 := by
      rw [← Real.rpow_add hr]
      norm_num
    have hRexp : (-(2 * (3 / 4 : ℝ))) = -(3 / 2 : ℝ) := by norm_num
    calc
      _ ≤ R * cubeFractionalSqNorm hd 0 1 h1 threeQuarterOrder
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 := by
        simpa [R, cubeFractionalSqNorm, threeQuarterOrder, hRexp] using hN
      _ ≤ R * (Cunit * (Jc.lam (0 : SpatialCoordinates d) 1 h1 b
          (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹ *
        sobolevCoefficientForm b (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)) (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1))) :=
        mul_le_mul_of_nonneg_left h0 (le_of_lt hR)
      _ = _ := by
        dsimp [Cc]
        rw [hlam, hE]
        exact aux_lem_as_coarse_arith R Cunit
          (r ^ ((2 : ℝ) - (d : ℝ)))
          (Jc.lam (0 : SpatialCoordinates d) 1 h1 b
            (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹
          (r ^ ((d : ℝ) - 2))
          (sobolevCoefficientForm b (w : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 h1)) (w : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 h1))) hpow
  · intro v
    obtain ⟨w, hwval, hwgrad⟩ :=
      _root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_meanZero_pullback d z r hr h1 v
    have hfg : ∀ i : Fin 1, ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (fun _ : Fin 1 => (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) i x =
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) i
            (cubeDilation z 0 r x) := by
      intro i
      simpa using hwval
    have hN := aux_lem_as_coarse_fractional_dilation d 1 hd z 0 r hr h1
      threeQuarterOrder
      (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
      (fun _ : Fin 1 => (w : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) hfg
    have hE := _root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_energy_scaling d z r hr h1 a b
      (v : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) hb hwval hwgrad
    have h0 := (hunit (0 : SpatialCoordinates d) h1 b).2 w |>.2
    have hpow : r ^ ((2 : ℝ) - (d : ℝ)) * r ^ ((d : ℝ) - 2) = 1 := by
      rw [← Real.rpow_add hr]
      norm_num
    have hRexp : (-(2 * (3 / 4 : ℝ))) = -(3 / 2 : ℝ) := by norm_num
    calc
      _ ≤ R * cubeFractionalSqNorm hd 0 1 h1 threeQuarterOrder
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 := by
        simpa [R, cubeFractionalSqNorm, threeQuarterOrder, hRexp] using hN
      _ ≤ R * (Cunit * (Jc.lam (0 : SpatialCoordinates d) 1 h1 b
          (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹ *
        sobolevCoefficientForm b (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)) (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1))) :=
        mul_le_mul_of_nonneg_left h0 (le_of_lt hR)
      _ = _ := by
        dsimp [Cc]
        rw [hlam, hE]
        exact aux_lem_as_coarse_arith R Cunit
          (r ^ ((2 : ℝ) - (d : ℝ)))
          (Jc.lam (0 : SpatialCoordinates d) 1 h1 b
            (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹
          (r ^ ((d : ℝ) - 2))
          (sobolevCoefficientForm b (w : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 h1)) (w : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 h1))) hpow

theorem aux_lem_as_coarse_extension_small
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          C * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  exact (lem_extension d hd Jc Xc Sf).1 beta hbeta

theorem aux_lem_as_coarse_dilation_dist
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x y : SpatialCoordinates d) :
    dist (cubeDilation z (0 : SpatialCoordinates d) r x)
        (cubeDilation z (0 : SpatialCoordinates d) r y) =
      r * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hxy : cubeDilation z (0 : SpatialCoordinates d) r x -
      cubeDilation z (0 : SpatialCoordinates d) r y = r • (x - y) := by
    funext i
    simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem aux_lem_as_coarse_dilation_frontier
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x : SpatialCoordinates d)
    (hx : x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) :
    cubeDilation z (0 : SpatialCoordinates d) r x ∈
      frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  change x ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) at hx
  change cubeDilation z (0 : SpatialCoordinates d) r x ∈
    frontier (Metric.ball z (r / 2))
  rw [frontier_ball _ (by positivity)] at hx ⊢
  have hx' : dist x (0 : SpatialCoordinates d) = 1 / 2 := by
    simpa [Metric.mem_sphere] using hx
  have hzero : cubeDilation z (0 : SpatialCoordinates d) r
      (0 : SpatialCoordinates d) = z := by
    funext i
    simp [cubeDilation]
  have hd := aux_lem_as_coarse_dilation_dist d z r hr x (0 : SpatialCoordinates d)
  rw [hzero] at hd
  simpa [Metric.mem_sphere, hx', dist_eq_norm, div_eq_mul_inv] using hd

theorem aux_lem_as_coarse_dilation_holder
    (d : ℕ) (hd : 2 ≤ d) (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : SpatialCoordinates d → ℝ)
    (hG : IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :
    IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) ∧
    holderSeminorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) ≤
      r ^ beta * holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G ∧
    0 ≤ holderSeminorm beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) := by
  have hd0 : 0 < d := by omega
  let : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  have hunit : IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) := by
    rcases hG with ⟨C, hC⟩
    refine ⟨r ^ beta * C, ?_⟩
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    have hTx := aux_lem_as_coarse_dilation_frontier d z r hr x hx
    have hTy := aux_lem_as_coarse_dilation_frontier d z r hr y hy
    have hTxy : cubeDilation z (0 : SpatialCoordinates d) r x ≠
        cubeDilation z (0 : SpatialCoordinates d) r y := by
      intro h
      apply hxy
      exact (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').injective
        (by simpa using h)
    have hq := hC ⟨cubeDilation z (0 : SpatialCoordinates d) r x, hTx,
      cubeDilation z (0 : SpatialCoordinates d) r y, hTy, hTxy, rfl⟩
    have hd := sqrt_sum_sq_cubeDilation z (0 : SpatialCoordinates d) hr x y
    rw [hd] at hq
    obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply (Finset.sum_pos_iff_of_nonneg
        (fun j _ => sq_nonneg (x j - y j))).2
      exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
    have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      Real.sqrt_pos.mpr hsum
    have hden0 : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≠ 0 := hden.ne'
    change |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
        G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤
        r ^ beta * C
    calc
      |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
        r ^ beta *
          (|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
            G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
            (r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta) := by
              rw [Real.mul_rpow (le_of_lt hr) hden.le]
              field_simp [hden0]
      _ ≤ r ^ beta * C := by
        exact mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (le_of_lt hr) _)
  have hGbdd : BddAbove (holderRatioSet beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) := hG
  rcases hunit with ⟨C, hC⟩
  have hunitbdd : BddAbove (holderRatioSet beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x))) := ⟨C, hC⟩
  have hratio_nonempty :
      (holderRatioSet beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x))).Nonempty := by
    change (holderRatioSet beta
      (frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x))).Nonempty
    rw [frontier_ball _ (by norm_num)]
    rcases (NormedSpace.sphere_nonempty (E := SpatialCoordinates d)).mpr
      (by norm_num : (0 : ℝ) ≤ 1 / 2) with ⟨x, hx⟩
    have hxfront : x ∈ Metric.sphere (0 : SpatialCoordinates d) (1 / 2) := hx
    have hyfront : -x ∈ Metric.sphere (0 : SpatialCoordinates d) (1 / 2) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hx
    have hxnorm : ‖x‖ = (1 / 2 : ℝ) := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hx
    have hxy : x ≠ -x := by
      intro heq
      have hsum : x + x = 0 := eq_neg_iff_add_eq_zero.mp heq
      have hsmul : (2 : ℝ) • x = 0 := by simpa [two_smul] using hsum
      have hxzero : x = 0 := (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
      rw [hxzero] at hxnorm
      norm_num at hxnorm
    refine ⟨|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
        G (cubeDilation z (0 : SpatialCoordinates d) r (-x))| /
        (Real.sqrt (∑ j : Fin d, (x j - (-x) j) ^ 2)) ^ beta, ?_⟩
    exact ⟨x, hxfront, -x, hyfront, hxy, rfl⟩
  have hseminorm_nonneg : 0 ≤ holderSeminorm beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)))
      (fun x => G (cubeDilation z (0 : SpatialCoordinates d) r x)) := by
    unfold holderSeminorm
    have hratio' := hratio_nonempty
    rcases hratio' with ⟨q, hq⟩
    have hsup := le_csSup hunitbdd hq
    have hq0 : 0 ≤ q := by
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hq
      positivity
    exact hq0.trans hsup
  refine ⟨⟨C, hC⟩, ?_, hseminorm_nonneg⟩
  unfold holderSeminorm
  apply csSup_le hratio_nonempty
  rintro q ⟨x, hx, y, hy, hxy, rfl⟩
  have hTx := aux_lem_as_coarse_dilation_frontier d z r hr x hx
  have hTy := aux_lem_as_coarse_dilation_frontier d z r hr y hy
  have hTxy : cubeDilation z (0 : SpatialCoordinates d) r x ≠
      cubeDilation z (0 : SpatialCoordinates d) r y := by
    intro h
    apply hxy
    exact (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').injective
      (by simpa using h)
  have hd := sqrt_sum_sq_cubeDilation z (0 : SpatialCoordinates d) hr x y
  obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun j _ => sq_nonneg (x j - y j))).2
    exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
  have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
    Real.sqrt_pos.mpr hsum
  have hqmem :
      |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d,
          (cubeDilation z (0 : SpatialCoordinates d) r x j -
            cubeDilation z (0 : SpatialCoordinates d) r y j) ^ 2)) ^ beta ∈
      holderRatioSet beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
    exact ⟨cubeDilation z (0 : SpatialCoordinates d) r x, hTx,
      cubeDilation z (0 : SpatialCoordinates d) r y, hTy, hTxy, rfl⟩
  have hq := le_csSup hGbdd hqmem
  have heq :
      |G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
      r ^ beta *
        (|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d,
          (cubeDilation z (0 : SpatialCoordinates d) r x j -
            cubeDilation z (0 : SpatialCoordinates d) r y j) ^ 2)) ^ beta) := by
    rw [hd]
    rw [Real.mul_rpow (le_of_lt hr) hden.le]
    field_simp [hden.ne']
  calc
    _ = r ^ beta *
        (|G (cubeDilation z (0 : SpatialCoordinates d) r x) -
          G (cubeDilation z (0 : SpatialCoordinates d) r y)| /
        (Real.sqrt (∑ j : Fin d,
          (cubeDilation z (0 : SpatialCoordinates d) r x j -
            cubeDilation z (0 : SpatialCoordinates d) r y j) ^ 2)) ^ beta) := heq
    _ ≤ r ^ beta * sSup (holderRatioSet beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :=
      mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (le_of_lt hr) _)

theorem aux_lem_as_coarse_dilation_killed_pushforward
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) :
    ∃ w : killedSobolevGraph (centeredCube z r hr),
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z r hr)).1 x =
          (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1
            (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((w : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ) x =
          r⁻¹ * ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
            (cubeDilation (0 : SpatialCoordinates d) z r⁻¹ x)) := by
  obtain ⟨u, hu_val, hu_grad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  have hgeom := aux_coercivity_dilation_cube_geometry d z r hr h1
  have htranslate : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    hgeom.1
  have hscale : (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    hgeom.2
  let U1 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  let U0 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))
  have hinv : (r⁻¹ : ℝ) • (r • U1) = U1 := by
    ext x
    constructor
    · intro hx
      have hx' : r • x ∈ r • U1 :=
        by simpa only [inv_inv] using
          (Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne')
            (r • U1) x).mp hx
      have hx'' : r⁻¹ • (r • x) ∈ U1 :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' U1 (r • x)).mp hx'
      simpa [smul_smul, hr.ne'] using hx''
    · intro hx
      have hx' : r • x ∈ r • U1 := by
        apply (Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' U1 (r • x)).mpr
        simpa [smul_smul, hr.ne'] using hx
      exact (Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne')
        (r • U1) x).mpr (by simpa only [inv_inv] using hx')
  let ucast : Homogenization.H10Function ((r⁻¹ : ℝ) • (r • U1)) := hinv.symm ▸ u
  have hucast_val : ucast.toFun = u.toFun := by
    simpa [ucast] using
      (_root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_h10_cast_toFun hinv.symm u)
  have hucast_grad : ucast.grad = u.grad := by
    simpa [ucast] using
      (_root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_h10_cast_grad hinv.symm u)
  let uS : Homogenization.H10Function (r • U1) :=
    Homogenization.H10Function.unscale (inv_pos.mpr hr) ucast
  have hscale' : U0 = r • U1 := by simpa [U0, U1] using hscale
  let u0 : Homogenization.H10Function U0 := hscale'.symm ▸ uS
  let htranslate' : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z U0 := by simpa [U0] using htranslate
  let uT : Homogenization.H10Function (Homogenization.translateSet z U0) :=
    Homogenization.H10Function.translate u0 z
  let wNative : Homogenization.H10Function
      (centeredCube z r hr : Set (SpatialCoordinates d)) := htranslate'.symm ▸ uT
  obtain ⟨w, hw_val, hw_grad⟩ :=
    _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 wNative
  have hwNative_val : wNative.toH1Function.toFun = uT.toH1Function.toFun := by
    simpa [wNative] using
      (_root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_h10_cast_toFun htranslate'.symm uT)
  have hwNative_grad : wNative.toH1Function.grad = uT.toH1Function.grad := by
    simpa [wNative] using
      (_root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_h10_cast_grad htranslate'.symm uT)
  have hu0_val : u0.toH1Function.toFun = uS.toH1Function.toFun := by
    simpa [u0] using
      (_root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_h10_cast_toFun hscale'.symm uS)
  have hu0_grad : u0.toH1Function.grad = uS.toH1Function.grad := by
    simpa [u0] using
      (_root_.SubdiffusiveProcess.Paper.aux_coercivity_dilation_h10_cast_grad hscale'.symm uS)
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw_val] with x hx
    rw [hx]
    rw [hwNative_val,
      Homogenization.H10Function.translate_toH1Function,
      Homogenization.H1Function.translate_toFun]
    change u0.toH1Function.toFun (x - z) = _
    rw [hu0_val]
    change (Homogenization.H10Function.unscale (inv_pos.mpr hr) ucast).toH1Function.toFun
      (x - z) = _
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_toFun]
    change ucast.toH1Function.toFun (r⁻¹ • (x - z)) = _
    rw [hucast_val]
    rw [hu_val]
    congr 1 ; funext i ; simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  · intro i
    filter_upwards [hw_grad i] with x hx
    rw [hx]
    rw [hwNative_grad,
      Homogenization.H10Function.translate_toH1Function,
      Homogenization.H1Function.translate_grad]
    rw [hu0_grad]
    change (Homogenization.H10Function.unscale (inv_pos.mpr hr) ucast).toH1Function.grad
      (x - z) i = _
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_grad]
    change (r⁻¹ • ucast.toH1Function.grad (r⁻¹ • (x - z))) i = _
    rw [hucast_grad]
    rw [hu_grad]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 2 ; funext j ;
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]

theorem aux_lem_as_coarse_large_extension
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (_Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (_Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (_hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (CE : ℝ) (hCE : 0 < CE)
    (hEsmall : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (_hr1 : 1 < r)
    (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (G : SpatialCoordinates d → ℝ)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hG : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hHolder : IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G)
    (hEq : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G) :
    dirichletResponse (killedResponseSpace hP) a b ≤
        CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
          r ^ ((d : ℝ) - 2) *
          (r ^ beta * holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  let h1 : (0 : ℝ) < 1 := one_pos
  have hd0 : 0 < d := by omega
  let : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    _root_.SubdiffusiveProcess.isOpenBoundedConvexDomain_centeredCube
      (0 : SpatialCoordinates d) h1
  obtain ⟨hPunit, _⟩ :=
    exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) 1 h1) hgeom
  obtain ⟨a', ha'⟩ :=
    _root_.SubdiffusiveProcess.Paper.dilation_coefficient_transport d z 0 r hr h1 a
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    cubeDilation z (0 : SpatialCoordinates d) r
  let G' : SpatialCoordinates d → ℝ := fun x => G (T x)
  have hclosed : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), T x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    change x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) at hx
    change T x ∈ Metric.closedBall z (r / 2)
    have hzero : cubeDilation z (0 : SpatialCoordinates d) r
        (0 : SpatialCoordinates d) = z := by
      funext i
      simp [cubeDilation]
    have hdT := aux_lem_as_coarse_dilation_dist d z r hr x
      (0 : SpatialCoordinates d)
    rw [hzero] at hdT
    change cubeDilation z (0 : SpatialCoordinates d) r x ∈
      Metric.closedBall z (r / 2)
    rw [Metric.mem_closedBall, hdT]
    have hmul := mul_le_mul_of_nonneg_left hx hr.le
    convert hmul using 1 ; ring
  have hG' : ContinuousOn G'
      (closedCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
    dsimp [G']
    exact hG.comp (continuous_cubeDilation z 0 r).continuousOn hclosed
  obtain ⟨hHolder', hHolderSeminorm, hHolderNonneg⟩ :=
    aux_lem_as_coarse_dilation_holder d hd beta z r hr G hHolder
  obtain ⟨b0, hb0val, hb0grad⟩ :=
    aux_coercivity_dilation_weak_pullback d z r hr h1 b
  have hqmp : Measure.QuasiMeasurePreserving T
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine ⟨(continuous_cubeDilation z 0 r).measurable, ?_⟩
    rw [show Measure.map T
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) =
          Measure.map (cubeDilation z 0 r)
            (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) by rfl]
    rw [map_cubeDilation_restrict z 0 hr h1]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _
  have hcomp := hqmp.ae_eq_comp hEq
  have hEq' : ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))] G' := by
    filter_upwards [hb0val, hcomp] with x hxb hxc
    exact hxb.trans (by simpa [T, Function.comp_def] using hxc)
  have he := hEsmall (0 : SpatialCoordinates d) 1 h1 (by norm_num) hPunit a' G' b0
    hG' hHolder' hEq'
  have hLam : Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 =
      Jc.Lam (0 : SpatialCoordinates d) 1 h1 a' (0 : SpatialCoordinates d) 1
        ((beta - 1 / 2) / 4) 2 := by
    apply Jc.Lam_dilation z r hr a 0 h1 a'
    filter_upwards [ha'] with x hx
    simpa only [cubeDilation_apply, sub_zero] using! hx
  let v0 : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    dirichletMinimizer (killedResponseSpace hPunit) a' b0
  have hq0mem : (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) -
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) ∈
      killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) := by
    exact dirichletMinimizer_mem_affine (killedResponseSpace hPunit) a' b0
  let q0 : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    ⟨(v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) -
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)), hq0mem⟩
  obtain ⟨q, hqval, hqgrad⟩ :=
    aux_lem_as_coarse_dilation_killed_pushforward d z r hr h1 q0
  have hinvcomp : ∀ x : SpatialCoordinates d,
      cubeDilation (0 : SpatialCoordinates d) z r⁻¹
          (cubeDilation z (0 : SpatialCoordinates d) r x) = x := by
    intro x
    funext i
    simp [cubeDilation]
    field_simp [ne_of_gt hr]
  have hqcomp := hqmp.ae_eq_comp hqval
  have hqcomp' : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      ((q : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          (T x) =
        ((q0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
          SpatialCoordinates d → ℝ) x := by
    filter_upwards [hqcomp] with x hx
    simpa [T, Function.comp_def, hinvcomp x] using hx
  have hqgradcomp : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (T x) = r⁻¹ *
        ((q0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x := by
    intro i
    have h := hqmp.ae_eq_comp (hqgrad i)
    filter_upwards [h] with x hx
    simpa [T, Function.comp_def, hinvcomp x] using hx
  have hval :
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            (T x) + ((q : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            (T x) := by
    have hsub := Lp.coeFn_sub
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
      ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
    filter_upwards [hb0val, hqcomp', hsub] with x hxb hxq hy
    rw [← hxb, hxq]
    change (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x +
        ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 -
          (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) x
    calc
      _ = ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
          SpatialCoordinates d → ℝ) x +
          (((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
            SpatialCoordinates d → ℝ) x -
            ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
              SpatialCoordinates d → ℝ) x) := by ring
      _ = _ := by
        exact congrArg (fun t : ℝ =>
          ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
            SpatialCoordinates d → ℝ) x + t) hy.symm
  have hgrad : ∀ i : Fin d,
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => r * (((b : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x) + ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x)) := by
    intro i
    have hsub := Lp.coeFn_sub
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
      ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
    filter_upwards [hb0grad i, hqgradcomp i, hsub] with x hxb hxg hy
    rw [hxg]
    rw [mul_add, ← hxb]
    change (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i x =
      (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i x +
        r * (r⁻¹ * (((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i -
          (b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) x))
    rw [hy]
    field_simp [ne_of_gt hr]
    have hpoint :
        ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x =
          ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
            SpatialCoordinates d → ℝ) x +
            (((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
              SpatialCoordinates d → ℝ) x -
              ((b0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
                SpatialCoordinates d → ℝ) x) := by
      abel
    simpa only [Pi.sub_apply] using hpoint
  have hvalE :
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => (((b : SobolevData (centeredCube z r hr)) +
          (q : SobolevData (centeredCube z r hr))).1 : SpatialCoordinates d → ℝ)
            (T x) := by
    have hadd := Lp.coeFn_add
      ((b : SobolevData (centeredCube z r hr)).1)
      ((q : SobolevData (centeredCube z r hr)).1)
    have hadd' := hqmp.ae_eq_comp hadd
    filter_upwards [hval, hadd'] with x hxv hxa
    exact hxv.trans hxa.symm
  have hgradE : ∀ i : Fin d,
      ((v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
        SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))]
        fun x => r * ((((b : SobolevData (centeredCube z r hr)) +
          (q : SobolevData (centeredCube z r hr))).2 i : SpatialCoordinates d → ℝ)
            (T x)) := by
    intro i
    have hadd := Lp.coeFn_add
      ((b : SobolevData (centeredCube z r hr)).2 i)
      ((q : SobolevData (centeredCube z r hr)).2 i)
    have hadd' := hqmp.ae_eq_comp hadd
    filter_upwards [hgrad i, hadd'] with x hxv hxa
    have hcompadd :
        ((b : SobolevData (centeredCube z r hr)) +
          (q : SobolevData (centeredCube z r hr))).2 i =
          (b : SobolevData (centeredCube z r hr)).2 i +
            (q : SobolevData (centeredCube z r hr)).2 i := by
      rfl
    rw [hcompadd]
    have hxa2 :
        ((((b : SobolevData (centeredCube z r hr)).2 i) +
          ((q : SobolevData (centeredCube z r hr)).2 i)) :
            DomainL2 (centeredCube z r hr)) (T x) =
          ((b : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x) + ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (T x) := by
      simpa [Function.comp_def] using hxa
    calc
      _ = r * (((b : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (T x) + ((q : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (T x)) := hxv
      _ = _ := by rw [hxa2.symm]
  have henergy := aux_coercivity_dilation_energy_scaling d z r hr h1 a a'
    ((b : SobolevData (centeredCube z r hr)) + (q : SobolevData (centeredCube z r hr)))
    (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) ha' hvalE hgradE
  have hleast := (dirichletResponse_isLeast (killedResponseSpace hP) a b).2
    ⟨q, rfl⟩
  have hresp : dirichletResponse (killedResponseSpace hP) a b ≤
      r ^ ((d : ℝ) - 2) * dirichletResponse
        (killedResponseSpace hPunit) a' b0 := by
    calc
      _ ≤ sobolevCoefficientForm a
          ((b : SobolevData (centeredCube z r hr)) +
            (q : SobolevData (centeredCube z r hr)))
          ((b : SobolevData (centeredCube z r hr)) +
            (q : SobolevData (centeredCube z r hr))) := hleast
      _ = r ^ ((d : ℝ) - 2) * sobolevCoefficientForm a'
          (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
          (v0 : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) := henergy
      _ = _ := by simp [v0, dirichletResponse]
  refine ?_
  have he' : dirichletResponse (killedResponseSpace hPunit) a' b0 ≤
      CE * Jc.Lam (0 : SpatialCoordinates d) 1 h1 a' (0 : SpatialCoordinates d) 1
        ((beta - 1 / 2) / 4) 2 *
        (holderSeminorm beta
          (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 := by
    simpa [G'] using he
  have he'' : dirichletResponse (killedResponseSpace hPunit) a' b0 ≤
      CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
        (holderSeminorm beta
          (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 := by
    rw [hLam]
    exact he'
  have hsq :
      (holderSeminorm beta
          (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 ≤
        (r ^ beta * holderSeminorm beta
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
    have hnonneg : 0 ≤ holderSeminorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G' := by
      simpa [G'] using hHolderNonneg
    have hright : 0 ≤ r ^ beta * holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G :=
      hnonneg.trans hHolderSeminorm
    nlinarith
  have hcoef : 0 ≤ CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
      r ^ ((d : ℝ) - 2) := by
    have hLamPos : 0 < Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 :=
      Jc.Lam_pos z r hr a z r ((beta - 1 / 2) / 4) 2
    exact mul_nonneg
      (mul_nonneg (le_of_lt hCE) (le_of_lt hLamPos))
      (le_of_lt (Real.rpow_pos_of_pos hr _))
  calc
    dirichletResponse (killedResponseSpace hP) a b ≤
        r ^ ((d : ℝ) - 2) *
          dirichletResponse (killedResponseSpace hPunit) a' b0 := hresp
    _ ≤ r ^ ((d : ℝ) - 2) *
        (CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
          (holderSeminorm beta
            (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2) := by
      exact mul_le_mul_of_nonneg_left he''
        (le_of_lt (Real.rpow_pos_of_pos hr _))
    _ ≤ CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
        r ^ ((d : ℝ) - 2) *
          (r ^ beta * holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsq hcoef
      calc
        _ = (CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
            r ^ ((d : ℝ) - 2)) *
              (holderSeminorm beta
                (frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) G') ^ 2 := by ring
        _ ≤ (CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
            r ^ ((d : ℝ) - 2)) *
              (r ^ beta * holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := hmul
        _ = _ := by ring
    _ = _ := by ring


theorem aux_lem_as_coarse_extension_finalize
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hfun : Bool → BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (CE : ℝ) (hCE : 0 < CE)
    (hEsmall : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          CE * Jc.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)
    (Le K : ℝ) (hLamLe : ∀ (withIR : Bool) (N : ℕ),
      Jc.Lam z r hr (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr) z r
        ((beta - 1 / 2) / 4) 2 ≤ Le)
    (hK : CE * Le ≤ K) :
    ∀ (withIR : Bool) (N : ℕ)
      (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr) b ≤
        K * r ^ ((d : ℝ) - 2) *
          (r ^ beta * holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  intro withIR N hP G b hG hHolder hEq
  let A : PositiveCoefficient (centeredCube z r hr) :=
    cutoffPositiveCoefficient M (Hfun withIR) ω N z hr
  let L : ℝ := Jc.Lam z r hr A z r ((beta - 1 / 2) / 4) 2
  let R : ℝ := r ^ ((d : ℝ) - 2)
  let S : ℝ :=
    (r ^ beta * holderSeminorm beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2
  have hL : L ≤ Le := by
    exact hLamLe withIR N
  have hDE : CE * L ≤ CE * Le :=
    mul_le_mul_of_nonneg_left hL hCE.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact le_of_lt (Real.rpow_pos_of_pos hr _)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact sq_nonneg _
  have hraw : dirichletResponse (killedResponseSpace hP) A b ≤ CE * L * R * S := by
    by_cases hrle : r ≤ 1
    · have he := hEsmall z r hr hrle hP A G b hG hHolder hEq
      exact he
    · have he := aux_lem_as_coarse_large_extension d hd Jc Xc Sf beta hbeta
        CE hCE hEsmall z r hr (lt_of_not_ge hrle) hP A G b hG hHolder hEq
      exact he
  change dirichletResponse (killedResponseSpace hP) A b ≤ K * R * S
  calc
    _ ≤ CE * L * R * S := hraw
    _ ≤ CE * Le * R * S := by
      calc
        _ = (CE * L) * (R * S) := by ring
        _ ≤ (CE * Le) * (R * S) :=
          mul_le_mul_of_nonneg_right hDE (mul_nonneg hR hS)
        _ = _ := by ring
    _ ≤ K * R * S := by
      calc
        _ = (CE * Le) * (R * S) := by ring
        _ ≤ K * (R * S) :=
          mul_le_mul_of_nonneg_right hK (mul_nonneg hR hS)
        _ = _ := by ring

/-- The deterministic translation of the whole bilateral field by `w`, exactly the map of
`prop_as_response_bank_shift_invariance`: every layer is precomposed with `x ↦ w + x`. -/
def aux_lem_as_coarse_shift (d : ℕ) (w : SpatialCoordinates d) (om : BilateralField d) :
    BilateralField d :=
  fun j => (om j).comp
    (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
      C(SpatialCoordinates d, SpatialCoordinates d))

theorem aux_lem_as_coarse_shift_apply (d : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) (j : ℤ) (x : SpatialCoordinates d) :
    aux_lem_as_coarse_shift d w om j x = om j (w + x) := by
  have hx : cubeDilation w 0 1 x = w + x := by
    funext i
    simp [cubeDilation]
  simp [aux_lem_as_coarse_shift, hx]

/-- Almost-sure properties are transported by the translation, which preserves the
common-scale product law (`prop_as_response_bank_shift_invariance`). -/
theorem aux_lem_as_coarse_shift_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (w : SpatialCoordinates d)
    {P : BilateralField d → Prop}
    (hP : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, P om) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, P (aux_lem_as_coarse_shift d w om) := by
  have hmap : Measure.map (aux_lem_as_coarse_shift d w) (chaosSampleLaw M).toMeasure =
      (chaosSampleLaw M).toMeasure :=
    prop_as_response_bank_shift_invariance d M w
  have hae : AEMeasurable (aux_lem_as_coarse_shift d w) (chaosSampleLaw M).toMeasure := by
    apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro j
    exact (ContinuousMap.compRightContinuousMap ℝ
      (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d))).continuous.measurable.comp
      (measurable_pi_apply j)
  refine ae_of_ae_map hae ?_
  rw [hmap]
  exact hP

/-- Translation of the infrared partial sums: they are anchored at the origin, so the
translated sum is the original one recentred at `w`. -/
theorem aux_lem_as_coarse_infraredPartialSum_shift (d : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) (L : ℕ) (x : SpatialCoordinates d) :
    infraredPartialSum (aux_lem_as_coarse_shift d w om) L x =
      infraredPartialSum om L (w + x) - infraredPartialSum om L w := by
  unfold infraredPartialSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, aux_lem_as_coarse_shift_apply, add_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The infrared field transforms by translation and recentring, almost surely. -/
theorem aux_lem_as_coarse_ir_shift {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (w : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      H (aux_lem_as_coarse_shift d w om) x = H om (w + x) - H om w := by
  have h1 := hH.2
  have h2 := aux_lem_as_coarse_shift_ae M w h1
  filter_upwards [h1, h2] with om h1 h2
  intro x
  have hA : Tendsto (fun L => infraredPartialSum (aux_lem_as_coarse_shift d w om) L x) atTop
      (nhds (H (aux_lem_as_coarse_shift d w om) x)) :=
    ((continuous_eval_const x).tendsto _).comp h2
  have hB : Tendsto (fun L => infraredPartialSum om L (w + x)) atTop (nhds (H om (w + x))) :=
    ((continuous_eval_const (w + x)).tendsto _).comp h1
  have hC : Tendsto (fun L => infraredPartialSum om L w) atTop (nhds (H om w)) :=
    ((continuous_eval_const w).tendsto _).comp h1
  have hD : Tendsto (fun L => infraredPartialSum (aux_lem_as_coarse_shift d w om) L x) atTop
      (nhds (H om (w + x) - H om w)) := by
    simp only [aux_lem_as_coarse_infraredPartialSum_shift]
    exact hB.sub hC
  exact tendsto_nhds_unique hA hD

/-- The cutoff coefficient of the translated field is the translated coefficient times the
constant infrared recentring factor. -/
theorem aux_lem_as_coarse_cutoff_shift {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (om : BilateralField d)
    (hHw : ∀ x : SpatialCoordinates d,
      H (aux_lem_as_coarse_shift d w om) x = H om (w + x) - H om w)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H (aux_lem_as_coarse_shift d w om) N x =
      cutoffCoefficient M H om N (w + x) * Real.exp (-H om w) := by
  unfold cutoffCoefficient cutoffPotential
  rw [hHw x]
  simp only [aux_lem_as_coarse_shift_apply]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Removing the infrared field multiplies the cutoff coefficient by `e^{-H}`. -/
theorem aux_lem_as_coarse_cutoff_remove_ir {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x =
      cutoffCoefficient M H om N x * Real.exp (-H om x) := by
  unfold cutoffCoefficient cutoffPotential
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [ContinuousMap.zero_apply]
  ring

/-- A positive quantity `a = b e^{c}` with `|c| ≤ E` satisfies `a + a⁻¹ ≤ e^E (b + b⁻¹)`. -/
theorem aux_lem_as_coarse_exp_factor (a b c E : ℝ) (hb : 0 < b)
    (hab : a = b * Real.exp c) (hc : |c| ≤ E) :
    a + a⁻¹ ≤ Real.exp E * (b + b⁻¹) := by
  have h1 : Real.exp c ≤ Real.exp E := Real.exp_le_exp.mpr ((le_abs_self c).trans hc)
  have h2 : Real.exp (-c) ≤ Real.exp E :=
    Real.exp_le_exp.mpr ((neg_le_abs c).trans hc)
  have hainv : a⁻¹ = b⁻¹ * Real.exp (-c) := by
    rw [hab, mul_inv, Real.exp_neg]
  have hbinv : 0 < b⁻¹ := inv_pos.mpr hb
  rw [hainv, hab, mul_add]
  have e1 : b * Real.exp c ≤ Real.exp E * b := by
    rw [mul_comm (Real.exp E)]
    exact mul_le_mul_of_nonneg_left h1 hb.le
  have e2 : b⁻¹ * Real.exp (-c) ≤ Real.exp E * b⁻¹ := by
    rw [mul_comm (Real.exp E)]
    exact mul_le_mul_of_nonneg_left h2 hbinv.le
  exact add_le_add e1 e2

/-- **Reference-cube subwavelength envelope.**  `lem_extremes` on the fixed unit cube at the
origin and the subwavelength supplier give a disorder threshold chosen from `s` alone. -/
theorem aux_lem_as_coarse_ref_extremes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
          ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
            (3 : ℝ) ^ (-(s * (N : ℝ))) *
              (cutoffCoefficient M H om N x + (cutoffCoefficient M H om N x)⁻¹) ≤ K := by
  have hext := aux_lem_extremes_compat d hd (0 : SpatialCoordinates d) 1 one_pos 1 le_rfl
  rcases hext with ⟨Cp, Cd, cd, hCp, hCd, hcd, hext⟩
  have hrate := aux_lem_as_coarse_subwave_supplier_rate s Cp Cd hs.1 hCp hCd
  rcases hrate with ⟨dr, gam, hdr, hgam, hgamlt, hrate⟩
  refine ⟨min cd dr, lt_min hcd hdr, ?_⟩
  intro M H hH hdel
  have hdcd : M.delta ≤ cd / 1 := by
    rw [div_one]
    exact hdel.trans (min_le_left _ _)
  have hM := hext M H hH hdcd
  rcases hM with ⟨D, mlow, mhigh, _hD0, hae, _hDmem, hmem, _hDmom, hmom⟩
  have hsup := lem_as_coarse_subwave_supplier d hd M (0 : SpatialCoordinates d) 1 one_pos
    s 1 hs le_rfl (fun _ => H) (fun _ => mlow) (fun _ => mhigh) Cp Cd gam hCp
    ⟨hgam, hrate M.delta M.shellPrefix.delta_pos.le (hdel.trans (min_le_right _ _)), hgamlt⟩
    (fun _ => by
      filter_upwards [hae] with om hom
      exact fun N => (hom N).2)
    (fun _ N => hmem N)
    (fun _ N => hmom N)
  filter_upwards [hsup, hae] with om hom hae
  rcases hom with ⟨Ksub, hKsub, hbound⟩
  refine ⟨Ksub, hKsub, ?_⟩
  intro N x hx
  have hb := hbound true 0 N (Nat.zero_le N)
  have hlo := (hae N).2.1
  have hx' := (hae N).2.2 x hx
  have hA : 0 < cutoffCoefficient M H om N x := hlo.trans_le hx'.1
  have hinv : (cutoffCoefficient M H om N x)⁻¹ ≤ (mlow N om)⁻¹ :=
    (inv_le_inv₀ hA hlo).mpr hx'.1
  have hsum : cutoffCoefficient M H om N x + (cutoffCoefficient M H om N x)⁻¹ ≤
      mhigh N om + (mlow N om)⁻¹ := add_le_add hx'.2 hinv
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hb

/-- A closed root is covered by finitely many closed unit cubes centred in the root. -/
theorem aux_lem_as_coarse_unit_cover {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ t : Finset (SpatialCoordinates d),
      (∀ w ∈ t, w ∈ (closedCube z r hr : Set (SpatialCoordinates d))) ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), ∃ w ∈ t,
        x - w ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) := by
  obtain ⟨t, hts, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall z (r / 2)) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨htfin.toFinset, ?_, ?_⟩
  · intro w hw
    exact hts (htfin.mem_toFinset.mp hw)
  · intro x hx
    have hx' := hcover (show x ∈ Metric.closedBall z (r / 2) from hx)
    rcases Set.mem_iUnion₂.mp hx' with ⟨w, hw, hxw⟩
    refine ⟨w, htfin.mem_toFinset.mpr hw, ?_⟩
    change x - w ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2)
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact (Metric.mem_ball.mp hxw).le

/-- Deterministic combination of the reference bound, the translation factor and the
infrared-removal factor at one point. -/
theorem aux_lem_as_coarse_point_chain (P A A0 b Kw h Ksum : ℝ) (hP : 0 ≤ P)
    (hh : 0 ≤ h) (hb : 0 < b)
    (hA : A + A⁻¹ ≤ Real.exp h * (b + b⁻¹))
    (hA0 : A0 + A0⁻¹ ≤ Real.exp h * (A + A⁻¹))
    (hbound : P * (b + b⁻¹) ≤ Kw) (hKw : Kw ≤ Ksum) :
    P * (A + A⁻¹) ≤ Real.exp (2 * h) * Ksum + 1 ∧
      P * (A0 + A0⁻¹) ≤ Real.exp (2 * h) * Ksum + 1 := by
  have he1 : 1 ≤ Real.exp h := Real.one_le_exp hh
  have he2 : Real.exp (2 * h) = Real.exp h * Real.exp h := by
    rw [← Real.exp_add]; ring_nf
  have hbb : 0 ≤ b + b⁻¹ := by positivity
  have hKw0 : 0 ≤ Kw := le_trans (mul_nonneg hP hbb) hbound
  have hstep1 : P * (A + A⁻¹) ≤ Real.exp h * Kw := by
    calc P * (A + A⁻¹) ≤ P * (Real.exp h * (b + b⁻¹)) := mul_le_mul_of_nonneg_left hA hP
      _ = Real.exp h * (P * (b + b⁻¹)) := by ring
      _ ≤ Real.exp h * Kw := mul_le_mul_of_nonneg_left hbound (Real.exp_pos h).le
  have hstep2 : Real.exp h * Kw ≤ Real.exp (2 * h) * Ksum := by
    rw [he2]
    calc Real.exp h * Kw ≤ Real.exp h * Real.exp h * Kw := by
          have := mul_le_mul_of_nonneg_right he1 hKw0
          nlinarith [Real.exp_pos h]
      _ ≤ Real.exp h * Real.exp h * Ksum :=
          mul_le_mul_of_nonneg_left hKw (by positivity)
  have hAA : 0 ≤ P * (A + A⁻¹) ∨ True := Or.inr trivial
  clear hAA
  constructor
  · linarith
  · have hstep0 : P * (A0 + A0⁻¹) ≤ Real.exp h * (P * (A + A⁻¹)) := by
      calc P * (A0 + A0⁻¹) ≤ P * (Real.exp h * (A + A⁻¹)) := mul_le_mul_of_nonneg_left hA0 hP
        _ = Real.exp h * (P * (A + A⁻¹)) := by ring
    have h3 : Real.exp h * (P * (A + A⁻¹)) ≤ Real.exp h * (Real.exp h * Kw) :=
      mul_le_mul_of_nonneg_left hstep1 (Real.exp_pos h).le
    have h4 : Real.exp h * (Real.exp h * Kw) ≤ Real.exp (2 * h) * Ksum := by
      rw [he2, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hKw (by positivity)
    linarith

/-- **Root subwavelength envelope with a root-independent disorder threshold.**  The
reference-cube bound is moved to every unit cube by translation invariance of the law, and a
finite cover of the closed root gives one random constant for both infrared conventions. -/
theorem aux_lem_as_coarse_root_extremes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir → M.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ withIR : Bool, ∀ N : ℕ,
          ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            (3 : ℝ) ^ (-(s * (N : ℝ))) *
              (cutoffCoefficient M
                  (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x +
                (cutoffCoefficient M
                  (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x)⁻¹) ≤
              K := by
  obtain ⟨delta0, hdelta0, href⟩ := aux_lem_as_coarse_ref_extremes d hd s hs
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Hir hIR hdel z r hr
  obtain ⟨t, htroot, htcover⟩ := aux_lem_as_coarse_unit_cover z r hr
  have hall : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ w ∈ t,
      (∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
          (3 : ℝ) ^ (-(s * (N : ℝ))) *
            (cutoffCoefficient M Hir (aux_lem_as_coarse_shift d w om) N x +
              (cutoffCoefficient M Hir (aux_lem_as_coarse_shift d w om) N x)⁻¹) ≤ K) ∧
      (∀ x : SpatialCoordinates d,
        Hir (aux_lem_as_coarse_shift d w om) x = Hir om (w + x) - Hir om w) := by
    refine (Filter.eventually_all_finset t).2 ?_
    intro w _
    exact (aux_lem_as_coarse_shift_ae M w (href M Hir hIR hdel)).and
      (aux_lem_as_coarse_ir_shift M Hir hIR w)
  filter_upwards [hall] with om hom
  obtain ⟨h, hh⟩ : ∃ h : ℝ, ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |Hir om y| ≤ h := by
    obtain ⟨C, hC⟩ := (closedCube z r hr).isCompact.exists_bound_of_continuousOn
      (Hir om).continuous.continuousOn
    exact ⟨C, fun y hy => by simpa [Real.norm_eq_abs] using hC y hy⟩
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    rw [dist_self]
    positivity
  have hh0 : 0 ≤ h := (abs_nonneg _).trans (hh z hz)
  choose! Kw hKw using fun w hw => (hom w hw).1
  have hsum0 : 0 ≤ ∑ w ∈ t, Kw w := Finset.sum_nonneg fun w hw => (hKw w hw).1.le
  refine ⟨Real.exp (2 * h) * ∑ w ∈ t, Kw w + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg (Real.exp_pos _).le hsum0) one_pos, ?_⟩
  intro withIR N x hx
  obtain ⟨w, hwt, hxw⟩ := htcover x hx
  have hshift := aux_lem_as_coarse_cutoff_shift M Hir w om (hom w hwt).2 N (x - w)
  have hwx : w + (x - w) = x := by abel
  rw [hwx] at hshift
  have hb : 0 < cutoffCoefficient M Hir (aux_lem_as_coarse_shift d w om) N (x - w) :=
    cutoffCoefficient_pos M Hir _ N _
  have hA : cutoffCoefficient M Hir om N x =
      cutoffCoefficient M Hir (aux_lem_as_coarse_shift d w om) N (x - w) *
        Real.exp (Hir om w) := by
    rw [hshift, mul_assoc, ← Real.exp_add]
    simp
  have hAfac := aux_lem_as_coarse_exp_factor _ _ _ h hb hA (hh w (htroot w hwt))
  have hA0 := aux_lem_as_coarse_cutoff_remove_ir M Hir om N x
  have hA0fac := aux_lem_as_coarse_exp_factor _ _ _ h (cutoffCoefficient_pos M Hir om N x) hA0
    (by rw [abs_neg]; exact hh x hx)
  have hchain := aux_lem_as_coarse_point_chain ((3 : ℝ) ^ (-(s * (N : ℝ))))
    (cutoffCoefficient M Hir om N x)
    (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x)
    (cutoffCoefficient M Hir (aux_lem_as_coarse_shift d w om) N (x - w)) (Kw w) h
    (∑ w ∈ t, Kw w) (by positivity) hh0 hb hAfac hA0fac ((hKw w hwt).2 N (x - w) hxw)
    (Finset.single_le_sum (fun w hw => (hKw w hw).1.le) hwt)
  cases withIR with
  | true => exact hchain.1
  | false => exact hchain.2

/-- The pointwise maximum of `A_N` on the closed root. -/
def aux_lem_as_coarse_mhigh {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : ℕ → BilateralField d → ℝ :=
  fun N om => sSup (cutoffCoefficient M H om N '' (closedCube z r hr : Set (SpatialCoordinates d)))

/-- The pointwise minimum of `A_N` on the closed root. -/
def aux_lem_as_coarse_mlow {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : ℕ → BilateralField d → ℝ :=
  fun N om => sInf (cutoffCoefficient M H om N '' (closedCube z r hr : Set (SpatialCoordinates d)))

/-- Both extremes are attained on the closed root, and they bracket `A_N` there. -/
theorem aux_lem_as_coarse_mext {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) (om : BilateralField d) :
    (∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      aux_lem_as_coarse_mhigh M H z r hr N om = cutoffCoefficient M H om N x) ∧
    (∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      aux_lem_as_coarse_mlow M H z r hr N om = cutoffCoefficient M H om N x) ∧
    0 < aux_lem_as_coarse_mlow M H z r hr N om ∧
    ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      aux_lem_as_coarse_mlow M H z r hr N om ≤ cutoffCoefficient M H om N x ∧
        cutoffCoefficient M H om N x ≤ aux_lem_as_coarse_mhigh M H z r hr N om := by
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    rw [dist_self]
    positivity
  have hK : IsCompact (cutoffCoefficient M H om N ''
      (closedCube z r hr : Set (SpatialCoordinates d))) :=
    (closedCube z r hr).isCompact.image (cutoffCoefficient_continuous M H om N)
  have hne : (cutoffCoefficient M H om N ''
      (closedCube z r hr : Set (SpatialCoordinates d))).Nonempty := ⟨_, z, hz, rfl⟩
  obtain ⟨x1, hx1, hx1e⟩ := hK.sSup_mem hne
  obtain ⟨x2, hx2, hx2e⟩ := hK.sInf_mem hne
  refine ⟨⟨x1, hx1, hx1e.symm⟩, ⟨x2, hx2, hx2e.symm⟩, ?_, ?_⟩
  · change 0 < sInf (cutoffCoefficient M H om N ''
      (closedCube z r hr : Set (SpatialCoordinates d)))
    rw [← hx2e]
    exact cutoffCoefficient_pos M H om N x2
  · intro x hx
    exact ⟨csInf_le hK.bddBelow ⟨x, hx, rfl⟩, le_csSup hK.bddAbove ⟨x, hx, rfl⟩⟩

/-- A bound on the two descendant maxima at root depth `n` bounds both cell matrices of
every depth-`n` cell of the root chart. -/
theorem aux_lem_as_coarse_cell_of_max {d : ℕ}
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) (n : ℕ) (X : ℝ)
    (hX : Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ)) a +
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ)) a ≤ X) :
    ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
      Homogenization.Book.Ch02.coarseBMatrixNorm R a ≤ X ∧
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R a ≤ X := by
  intro R hR
  have hR' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      (-(n : ℤ)) := by
    simpa [aux_lem_as_coarse_ms_desc, Homogenization.originCube] using hR
  have hb : Homogenization.Book.Ch02.coarseBMatrixNorm R a ≤
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ)) a := by
    unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
      Homogenization.Book.Ch02.finsetSupReal
    exact le_csSup ((Set.Finite.image _ (Finset.finite_toSet _)).bddAbove)
      ⟨R, Finset.mem_coe.mpr hR', rfl⟩
  have hs : Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R a ≤
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ)) a := by
    unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      Homogenization.Book.Ch02.finsetSupReal
    exact le_csSup ((Set.Finite.image _ (Finset.finite_toSet _)).bddAbove)
      ⟨R, Finset.mem_coe.mpr hR', rfl⟩
  have hb0 : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R a := norm_nonneg _
  have hs0 : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R a := norm_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- The late-cell envelope `3^{-oN}(max A_N + (min A_N)⁻¹)` from the pointwise root bound
at the smaller order `smin ≤ o`. -/
theorem aux_lem_as_coarse_late_envelope {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (o smin Kp : ℝ) (hsmin : smin ≤ o)
    (hpt : ∀ N : ℕ, ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (-(smin * (N : ℝ))) *
        (cutoffCoefficient M H om N x + (cutoffCoefficient M H om N x)⁻¹) ≤ Kp)
    (N : ℕ) :
    (3 : ℝ) ^ (-(o * (N : ℝ))) *
        (aux_lem_as_coarse_mhigh M H z r hr N om + (aux_lem_as_coarse_mlow M H z r hr N om)⁻¹) ≤
      2 * Kp := by
  obtain ⟨⟨x1, hx1, he1⟩, ⟨x2, hx2, he2⟩, _, _⟩ := aux_lem_as_coarse_mext M H z r hr N om
  have hp1 := hpt N x1 hx1
  have hp2 := hpt N x2 hx2
  have hA1 : 0 < cutoffCoefficient M H om N x1 := cutoffCoefficient_pos M H om N x1
  have hA2 : 0 < cutoffCoefficient M H om N x2 := cutoffCoefficient_pos M H om N x2
  have hpow : (3 : ℝ) ^ (-(o * (N : ℝ))) ≤ (3 : ℝ) ^ (-(smin * (N : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg (mul_le_mul_of_nonneg_right hsmin (Nat.cast_nonneg N)))
  have hP : 0 ≤ (3 : ℝ) ^ (-(smin * (N : ℝ))) := by positivity
  have hS : aux_lem_as_coarse_mhigh M H z r hr N om + (aux_lem_as_coarse_mlow M H z r hr N om)⁻¹ ≤
      (cutoffCoefficient M H om N x1 + (cutoffCoefficient M H om N x1)⁻¹) +
        (cutoffCoefficient M H om N x2 + (cutoffCoefficient M H om N x2)⁻¹) := by
    rw [he1, he2]
    have := inv_pos.mpr hA1
    linarith
  have hS0 : 0 ≤ aux_lem_as_coarse_mhigh M H z r hr N om +
      (aux_lem_as_coarse_mlow M H z r hr N om)⁻¹ := by
    rw [he1, he2]
    positivity
  calc (3 : ℝ) ^ (-(o * (N : ℝ))) *
        (aux_lem_as_coarse_mhigh M H z r hr N om + (aux_lem_as_coarse_mlow M H z r hr N om)⁻¹)
      ≤ (3 : ℝ) ^ (-(smin * (N : ℝ))) *
        (aux_lem_as_coarse_mhigh M H z r hr N om + (aux_lem_as_coarse_mlow M H z r hr N om)⁻¹) :=
        mul_le_mul_of_nonneg_right hpow hS0
    _ ≤ (3 : ℝ) ^ (-(smin * (N : ℝ))) *
        ((cutoffCoefficient M H om N x1 + (cutoffCoefficient M H om N x1)⁻¹) +
          (cutoffCoefficient M H om N x2 + (cutoffCoefficient M H om N x2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hS hP
    _ ≤ 2 * Kp := by rw [mul_add]; linarith

/-- **One convention, one order.**  The retained, deep and late-cell inputs at one sample give
one constant for `Λ_{o,q} + λ_{o,q}⁻¹`, `q ∈ {1,2}`, for every order `o ≥ smin`. -/
theorem aux_lem_as_coarse_conv_bound {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (smin rho theta xi : ℝ) (hrho : rho < smin) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hxi : xi ≤ (smin - rho) * theta)
    (Ksh Kp : ℝ) (hKsh : 0 ≤ Ksh) (Kdeep : ℕ → ℝ) (hKd : ∀ N, 0 ≤ Kdeep N)
    (hsh : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
          (Homogenization.originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) +
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
        Ksh * (3 : ℝ) ^ (rho * (k : ℝ)))
    (hdp : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (Kdeep N ≤ (3 : ℝ) ^ (xi * (N : ℝ)) ∧
        ∀ k : ℕ, (theta * (N : ℝ) < (k : ℝ)) ∧ k ≤ N →
          Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
              (Homogenization.originCube d 0) (-(k : ℤ))
              (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) +
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0) (-(k : ℤ))
              (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
            Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ))))
    (hpt : ∀ N : ℕ, ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (-(smin * (N : ℝ))) *
        (cutoffCoefficient M H om N x + (cutoffCoefficient M H om N x)⁻¹) ≤ Kp) :
    ∀ o : ℝ, o ∈ Set.Ioc (0 : ℝ) 1 → smin ≤ o →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
        Jc.Lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r o qe +
          (Jc.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r o qe)⁻¹ ≤ C := by
  intro o ho hso
  obtain ⟨N1, hN1⟩ := hsh
  obtain ⟨N2, hN2⟩ := hdp
  have hext : ∀ N : ℕ, 0 < aux_lem_as_coarse_mlow M H z r hr N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        aux_lem_as_coarse_mlow M H z r hr N om ≤ cutoffCoefficient M H om N x ∧
          cutoffCoefficient M H om N x ≤ aux_lem_as_coarse_mhigh M H z r hr N om :=
    fun N => ⟨(aux_lem_as_coarse_mext M H z r hr N om).2.2.1,
      (aux_lem_as_coarse_mext M H z r hr N om).2.2.2⟩
  have hcons := lem_as_coarse_scalar_consumer hd Jc M H om z r hr
    (aux_lem_as_coarse_mlow M H z r hr) (aux_lem_as_coarse_mhigh M H z r hr) hext 0 (max N1 N2)
  rcases hcons with ⟨hS, hsub⟩
  have hxio : xi ≤ (o - rho) * theta :=
    hxi.trans (mul_le_mul_of_nonneg_right (by linarith) htheta.le)
  exact lem_as_coarse_multiscale_assembly hd Jc z r hr
    (fun N => cutoffPositiveCoefficient M H om N z hr) o ho rho theta xi (by linarith)
    htheta.le htheta1.le hxio (max N1 N2) Ksh (2 * Kp) Kdeep
    (fun N => aux_lem_as_coarse_mhigh M H z r hr N om +
      (aux_lem_as_coarse_mlow M H z r hr N om)⁻¹)
    hKsh hKd hS
    (fun N hN => (hN2 N (le_trans (le_max_right _ _) hN)).1)
    (fun N _ => aux_lem_as_coarse_late_envelope M H om z r hr o smin Kp hso hpt N)
    (fun N hN n hn R hR => aux_lem_as_coarse_cell_of_max _ n _
      (hN1 N (le_trans (le_max_left _ _) hN) n hn) R hR)
    (fun N hN n hn hnN R hR => aux_lem_as_coarse_cell_of_max _ n _
      ((hN2 N (le_trans (le_max_right _ _) hN)).2 n ⟨hn, hnN⟩) R hR)
    (fun N hN n hn R hR => hsub N hN n (by omega) R hR)

/-- **Deterministic finish at one sample.**  Uniform first-clause bounds at the three orders
`s`, `1/8` (coercivity) and `(β-1/2)/4` (extension), in both infrared conventions, give the
four conclusions of the lemma with one constant. -/
theorem aux_lem_as_coarse_finish
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (s beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Ks K8 Ke : ℝ) (hKs : 0 < Ks)
    (hbs : ∀ (withIR : Bool) (N : ℕ) (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r s qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
            z r s qe)⁻¹ ≤ Ks)
    (hb8 : ∀ (withIR : Bool) (N : ℕ) (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
          z r (1 / 8 : ℝ) qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
            z r (1 / 8 : ℝ) qe)⁻¹ ≤ K8)
    (hbe : ∀ (withIR : Bool) (N : ℕ) (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
          z r ((beta - 1 / 2) / 4) qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
            z r ((beta - 1 / 2) / 4) qe)⁻¹ ≤ Ke) :
    ∃ K : ℝ, 0 < K ∧
      ∀ withIR : Bool,
        let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
          if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ));
        (∀ (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) → ∀ N : ℕ,
          Jc.Lam z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r s qe +
              (Jc.lam z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r s qe)⁻¹ ≤
            K) ∧
        (∀ N : ℕ, ∀ v : killedSobolevGraph (centeredCube z r hr),
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (v : SobolevData (centeredCube z r hr)).1 ≤
            K * sobolevCoefficientForm (cutoffPositiveCoefficient M Hc ω N z hr)
              (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) ∧
        (∀ N : ℕ, ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (v : SobolevData (centeredCube z r hr)).1 ≤
            K * sobolevCoefficientForm (cutoffPositiveCoefficient M Hc ω N z hr)
              (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) ∧
        (∀ (N : ℕ)
          (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
            ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
              C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
          (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
          ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
          IsHolderOn beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
          dirichletResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient M Hc ω N z hr) b ≤
            K * r ^ ((d : ℝ) - 2) *
            (r ^ beta *
                holderSeminorm beta
                  (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2) := by
  let Hfun : Bool → BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun b => if b then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
  have Ccoerc := aux_lem_as_coarse_coercivity d hd Jc Pc Sf z r hr
  rcases Ccoerc with ⟨Cc, hCc, hcoerc⟩
  have Cext := aux_lem_as_coarse_extension_small d hd Jc Xc Sf beta hbeta
  rcases Cext with ⟨CE, hCE, hEsmall⟩
  let K : ℝ := max (max Ks (Cc * K8)) (CE * Ke)
  have hK : 0 < K := lt_of_lt_of_le (lt_of_lt_of_le hKs (le_max_left _ _)) (le_max_left _ _)
  have hB : ∀ (b : Bool) (N : ℕ),
      (Jc.lam z r hr (cutoffPositiveCoefficient M (Hfun b) ω N z hr) z r (1 / 8 : ℝ) 1)⁻¹ ≤
        K8 := by
    intro b N
    have h := hb8 b N 1 (Or.inl rfl)
    have hL := (Jc.Lam_pos z r hr (cutoffPositiveCoefficient M (Hfun b) ω N z hr)
      z r (1 / 8 : ℝ) 1).le
    exact (le_add_of_nonneg_left hL).trans h
  have hLamLe : ∀ (b : Bool) (N : ℕ),
      Jc.Lam z r hr (cutoffPositiveCoefficient M (Hfun b) ω N z hr) z r
        ((beta - 1 / 2) / 4) 2 ≤ Ke := by
    intro b N
    have h := hbe b N 2 (Or.inr rfl)
    have hl := (inv_pos.2 (Jc.lam_pos z r hr (cutoffPositiveCoefficient M (Hfun b) ω N z hr)
      z r ((beta - 1 / 2) / 4) 2)).le
    exact (le_add_of_nonneg_right hl).trans h
  refine ⟨K, hK, ?_⟩
  intro withIR
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro qe hqe N
    exact (hbs withIR N qe hqe).trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro N v
    have hc := (hcoerc (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr)).1 v
    have hform : 0 ≤ sobolevCoefficientForm
        (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr)
        (v : SobolevData (centeredCube z r hr))
        (v : SobolevData (centeredCube z r hr)) :=
      sobolevCoefficientForm_nonneg _ _
    calc _ ≤ Cc * (Jc.lam z r hr (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr)
            z r (1 / 8 : ℝ) 1)⁻¹ * _ := hc
      _ ≤ Cc * K8 * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB withIR N) hCc.le) hform
      _ ≤ K * _ :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hform
  · intro N v
    have hc := (hcoerc (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr)).2 v
    have hform : 0 ≤ sobolevCoefficientForm
        (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr)
        (v : SobolevData (centeredCube z r hr))
        (v : SobolevData (centeredCube z r hr)) :=
      sobolevCoefficientForm_nonneg _ _
    calc _ ≤ Cc * (Jc.lam z r hr (cutoffPositiveCoefficient M (Hfun withIR) ω N z hr)
            z r (1 / 8 : ℝ) 1)⁻¹ * _ := hc
      _ ≤ Cc * K8 * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB withIR N) hCc.le) hform
      _ ≤ K * _ :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hform
  · exact aux_lem_as_coarse_extension_finalize d hd Jc Xc Sf beta hbeta M Hfun ω z r hr
      CE hCE hEsmall Ke K hLamLe (le_max_right _ _) withIR

/-- Both infrared conventions, from the per-convention bound. -/
theorem aux_lem_as_coarse_both {d : ℕ} (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (o : ℝ)
    (hconv : ∀ withIR : Bool, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r o qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
            z r o qe)⁻¹ ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (withIR : Bool) (N : ℕ) (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r o qe +
        (Jc.lam z r hr (cutoffPositiveCoefficient M
          (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
            z r o qe)⁻¹ ≤ C := by
  obtain ⟨Ct, hCt, ht⟩ := hconv true
  obtain ⟨Cf, _, hf⟩ := hconv false
  refine ⟨max Ct Cf, lt_max_of_lt_left hCt, ?_⟩
  intro withIR N qe hqe
  cases withIR with
  | true => exact (ht N qe hqe).trans (le_max_left _ _)
  | false => exact (hf N qe hqe).trans (le_max_right _ _)

/-- **One sample.**  The retained-grid (`lem_as_coarse_shallow_grid`), deep-grid
(`lem_as_coarse_deep_grid`) and root subwavelength outputs at a sample, with one common
retained fraction `theta` and cell rate `rho < smin/4 ≤ o/4` for all three orders
`o ∈ {s, 1/8, (β-1/2)/4}`, give the four conclusions of the lemma. -/
theorem aux_lem_as_coarse_rooted
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (s beta : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (smin rho theta xi : ℝ) (hsmin_s : smin ≤ s) (hsmin_8 : smin ≤ 1 / 8)
    (hsmin_e : smin ≤ (beta - 1 / 2) / 4) (hrho : rho < smin) (htheta : 0 < theta)
    (htheta1 : theta < 1) (hxi : xi ≤ (smin - rho) * theta)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : ∃ K : ℝ, 0 < K ∧
      ∀ withIR : Bool,
        let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
          if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
        ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
          ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
            Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                (Homogenization.originCube d 0) (-(k : ℤ))
                (Jc.chart z r hr
                  (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(k : ℤ))
                (Jc.chart z r hr
                  (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
              K * (3 : ℝ) ^ (rho * (k : ℝ)))
    (h2 : ∃ K_N : ℕ → ℝ, (∀ N, 0 < K_N N) ∧
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        (K_N N ≤ (3 : ℝ) ^ (xi * (N : ℝ)) ∧
        ∀ withIR : Bool,
          let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
            if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
          ∀ k : ℕ, (theta * (N : ℝ) < (k : ℝ)) ∧ k ≤ N →
            Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                (Homogenization.originCube d 0) (-(k : ℤ))
                (Jc.chart z r hr
                  (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(k : ℤ))
                (Jc.chart z r hr
                  (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
              K_N N * (3 : ℝ) ^ (rho * (k : ℝ))))
    (h3 : ∃ K : ℝ, 0 < K ∧ ∀ withIR : Bool, ∀ N : ℕ,
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        (3 : ℝ) ^ (-(smin * (N : ℝ))) *
          (cutoffCoefficient M
              (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x +
            (cutoffCoefficient M
              (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x)⁻¹) ≤
          K) :
    ∃ K : ℝ, 0 < K ∧
        ∀ withIR : Bool,
          let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
            if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ));
          (∀ (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) → ∀ N : ℕ,
            Jc.Lam z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r s qe +
                (Jc.lam z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r s qe)⁻¹ ≤
              K) ∧
          (∀ N : ℕ, ∀ v : killedSobolevGraph (centeredCube z r hr),
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K * sobolevCoefficientForm (cutoffPositiveCoefficient M Hc ω N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr))) ∧
          (∀ N : ℕ, ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K * sobolevCoefficientForm (cutoffPositiveCoefficient M Hc ω N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr))) ∧
          (∀ (N : ℕ)
            (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
              ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
                C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
            (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
            ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
            IsHolderOn beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
            dirichletResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient M Hc ω N z hr) b ≤
              K * r ^ ((d : ℝ) - 2) *
              (r ^ beta *
                  holderSeminorm beta
                    (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2) := by
  have hse : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by linarith [hbeta.1], by linarith [hbeta.2]⟩
  rcases h1 with ⟨Ksh, hKsh, hsh⟩
  rcases h2 with ⟨KN, hKN, N0d, hdp⟩
  rcases h3 with ⟨Kp, _, hpt⟩
  have hconv : ∀ withIR : Bool, ∀ o : ℝ, o ∈ Set.Ioc (0 : ℝ) 1 → smin ≤ o →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ qe : ℝ≥0∞, (qe = 1 ∨ qe = 2) →
        Jc.Lam z r hr (cutoffPositiveCoefficient M
            (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
            z r o qe +
          (Jc.lam z r hr (cutoffPositiveCoefficient M
            (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr)
              z r o qe)⁻¹ ≤ C := by
    intro withIR
    exact aux_lem_as_coarse_conv_bound hd Jc M
      (if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω z r hr
      smin rho theta xi hrho htheta htheta1 hxi Ksh Kp hKsh.le KN (fun N => (hKN N).le)
      (hsh withIR) ⟨N0d, fun N hN => ⟨(hdp N hN).1, (hdp N hN).2 withIR⟩⟩ (hpt withIR)
  have hS := aux_lem_as_coarse_both Jc M Hir ω z r hr s (fun b => hconv b s hs hsmin_s)
  have h8 := aux_lem_as_coarse_both Jc M Hir ω z r hr (1 / 8 : ℝ)
    (fun b => hconv b (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩ hsmin_8)
  have hE := aux_lem_as_coarse_both Jc M Hir ω z r hr ((beta - 1 / 2) / 4)
    (fun b => hconv b ((beta - 1 / 2) / 4) hse hsmin_e)
  rcases hS with ⟨Ks, hKs, hbs⟩
  rcases h8 with ⟨K8, _, hb8⟩
  rcases hE with ⟨Ke, _, hbe⟩
  exact aux_lem_as_coarse_finish d hd Jc Pc Xc Sf s beta hbeta M Hir ω z r hr Ks K8 Ke hKs
    hbs hb8 hbe

theorem lem_as_coarse
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (s beta : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ));
            (∀ (qe : ℝ≥0∞), (qe = 1 ∨ qe = 2) → ∀ N : ℕ,
              Jc.Lam z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r s qe +
                  (Jc.lam z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r s qe)⁻¹ ≤
                K) ∧
            (∀ N : ℕ, ∀ v : killedSobolevGraph (centeredCube z r hr),
              cubeFractionalSqNorm hd z r hr threeQuarterOrder
                  (v : SobolevData (centeredCube z r hr)).1 ≤
                K * sobolevCoefficientForm (cutoffPositiveCoefficient M Hc ω N z hr)
                  (v : SobolevData (centeredCube z r hr))
                  (v : SobolevData (centeredCube z r hr))) ∧
            (∀ N : ℕ, ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
              cubeFractionalSqNorm hd z r hr threeQuarterOrder
                  (v : SobolevData (centeredCube z r hr)).1 ≤
                K * sobolevCoefficientForm (cutoffPositiveCoefficient M Hc ω N z hr)
                  (v : SobolevData (centeredCube z r hr))
                  (v : SobolevData (centeredCube z r hr))) ∧
            (∀ (N : ℕ)
              (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
                ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
                  C * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
              (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
              ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
              IsHolderOn beta
                  (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
              dirichletResponse (killedResponseSpace hP)
                  (cutoffPositiveCoefficient M Hc ω N z hr) b ≤
                K * r ^ ((d : ℝ) - 2) *
                (r ^ beta *
                    holderSeminorm beta
                      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2) := by

  have hse : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by linarith [hbeta.1], by linarith [hbeta.2]⟩
  -- one common order `smin ≤ s, 1/8, (β-1/2)/4` for the cell rate, fixed before the model
  obtain ⟨smin, hsmin_def⟩ : ∃ smin : ℝ, smin = min s (min (1 / 8) ((beta - 1 / 2) / 4)) :=
    ⟨_, rfl⟩
  have hsmin_s : smin ≤ s := by rw [hsmin_def]; exact min_le_left _ _
  have hsmin_8 : smin ≤ 1 / 8 := by
    rw [hsmin_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hsmin_e : smin ≤ (beta - 1 / 2) / 4 := by
    rw [hsmin_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hsmin_pos : 0 < smin := by
    rw [hsmin_def]; exact lt_min hs.1 (lt_min (by norm_num) hse.1)
  have hsmin : smin ∈ Set.Ioc (0 : ℝ) 1 := ⟨hsmin_pos, hsmin_s.trans hs.2⟩
  obtain ⟨rho, hrho_def⟩ : ∃ rho : ℝ, rho = smin / 8 := ⟨_, rfl⟩
  have hrho : 0 < rho := by rw [hrho_def]; positivity
  have hrhos : rho < smin / 4 := by rw [hrho_def]; linarith
  -- the retained-grid child chooses one small `theta` and its threshold
  have hsh := lem_as_coarse_shallow_grid d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp smin rho hsmin hrho hrhos
  rcases hsh with ⟨theta, dsh, htheta, htheta1, hdsh, hsh⟩
  -- the deep-grid rate `xi < (smin - rho) theta` and its threshold
  obtain ⟨xi, hxi_def⟩ : ∃ xi : ℝ, xi = (smin - rho) * theta / 2 := ⟨_, rfl⟩
  have hgap : 0 < (smin - rho) * theta := mul_pos (by linarith) htheta
  have hxi : 0 < xi := by rw [hxi_def]; linarith
  have hxi_tail : xi < (smin - rho) * theta := by rw [hxi_def]; linarith
  have hdp := lem_as_coarse_deep_grid d hd Jc Xc Sf smin beta rho theta xi hsmin hbeta
    hrho hrhos htheta htheta1 hxi hxi_tail
  rcases hdp with ⟨ddp, hddp, hdp⟩
  -- the subwavelength threshold, from the reference unit cube only
  have hex := aux_lem_as_coarse_root_extremes d hd smin hsmin
  rcases hex with ⟨dex, hdex, hex⟩
  refine ⟨min dsh (min ddp dex), lt_min hdsh (lt_min hddp hdex), ?_⟩
  intro M Rm Sreg It Hir hIR hdel z r hr htri
  have hd1 : M.delta ≤ 1 := hdel.trans (min_le_left _ _)
  have hd0 : M.delta ≤ min dsh (min ddp dex) := hdel.trans (min_le_right _ _)
  have e1 := hsh M Rm Sreg It Hir hIR (le_min hd1 (hd0.trans (min_le_left _ _))) z r hr htri
  have e2 := hdp M Rm Hir hIR
    (le_min hd1 (hd0.trans ((min_le_right _ _).trans (min_le_left _ _)))) z r hr htri
  have e3 := hex M Hir hIR (hd0.trans ((min_le_right _ _).trans (min_le_right _ _))) z r hr
  filter_upwards [e1, e2, e3] with ω h1 h2 h3
  exact aux_lem_as_coarse_rooted d hd Jc Pc Xc Sf s beta hs hbeta smin rho theta xi
    hsmin_s hsmin_8 hsmin_e (by linarith) htheta htheta1 hxi_tail.le M Hir ω z r hr h1 h2 h3

end SubdiffusiveProcess.Paper
