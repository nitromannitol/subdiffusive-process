module

public import SubdiffusiveProcess.EllipticRegularity.Numeric
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The deterministic Besov chain behind `eq:mfd-1` gives `H^{3/4}`
coercivity on the unit cube for killed and mean-zero data. The positive
order `s ∈ (0,1/4)` is fixed before the embedding constant, which may depend
on `s`; one constant serves both classes.

The inputs identify the same positive-overlap fractional seminorms under
affine pullback: `in_poincare` at order `1-s` and
`SobolevFoundationalInput` at order `t`. The former supplies the negative
seminorm and centered/killed estimates, and `in_J` supplies the ellipticity
quantity and its monotonicity. The conclusions include finiteness of the
fractional seminorm before the real norm inequality. Weak `H¹` membership
supplies that finiteness through the foundational input. -/
private theorem aux_lane4_besov_h34_coercivity
    (d : ℕ) (hd : 2 ≤ d) (E : in_J d) (_P : in_poincare d hd E)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z 1 hr))
    (u : weakSobolevGraph (centeredCube z 1 hr))
    (hL : ‖(u : SobolevData (centeredCube z 1 hr)).1‖ /
        Real.sqrt (volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d))) ≤
      _P.C * (E.lam z 1 hr a z 1 1 1) ^ (-(1 / 2) : ℝ) *
        normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
          (sobolevGradient (u : SobolevData (centeredCube z 1 hr)))) :
    cubeFractionalL2Seminorm hd z 1 hr threeQuarterOrder
        (fun _ : Fin 1 => (u : SobolevData (centeredCube z 1 hr)).1) < ⊤ ∧
      cubeFractionalSqNorm hd z 1 hr threeQuarterOrder
          (u : SobolevData (centeredCube z 1 hr)).1 ≤
        (_S.CBesov s * _P.C ^ 2 * (_P.cssPow s 1 ^ 2 + 1)) *
          (E.lam z 1 hr a z 1 s 1)⁻¹ *
            sobolevCoefficientForm a (u : SobolevData (centeredCube z 1 hr))
              (u : SobolevData (centeredCube z 1 hr)) := by
  have hs01 : s ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · exact hs.1
    · linarith [hs.2]
  have ht01 : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have ht01oc : 1 - s ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · exact ht01.1
    · exact le_of_lt ht01.2
  have hfinite :
      (iSup (fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
          (fun x => (u : SobolevData (centeredCube z 1 hr)).1
            (fun i : Fin d => z i + 1 * x i))
          (_S.positive_integrable z 1 hr
            (u : SobolevData (centeredCube z 1 hr)).1) j)) < ⊤ := by
    simpa using _S.besov_finite_H1 z 1 hr (1 - s) ht01
      (u : weakSobolevGraph (centeredCube z 1 hr))
  have hmem :
      cubeFractionalL2Seminorm hd z 1 hr threeQuarterOrder
          (fun _ : Fin 1 => (u : SobolevData (centeredCube z 1 hr)).1) < ⊤ :=
    _S.h1_fractional_finite z 1 hr u
  have hvol : volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d)) = 1 :=
    _root_.SubdiffusiveProcess.EllipticRegularity.centeredCube_one_volume_real z hr
  have h3 :
      cubeFractionalSqNorm hd z 1 hr threeQuarterOrder
          (u : SobolevData (centeredCube z 1 hr)).1 ≤
        _S.CBesov s *
          (_S.besovSeminorm z 1 hr (1 - s)
              (u : SobolevData (centeredCube z 1 hr)).1 ^ 2 +
            (‖(u : SobolevData (centeredCube z 1 hr)).1‖ /
              Real.sqrt (volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d)))) ^ 2) := by
    have h3raw := _S.besov_embedding s hs z 1 hr (le_refl 1)
      ((u : SobolevData (centeredCube z 1 hr)).1) hfinite
    simpa [hvol] using h3raw
  have hbesov :
      _P.besovSeminorm z 1 hr (u : SobolevData (centeredCube z 1 hr)).1 s =
        _S.besovSeminorm z 1 hr (1 - s)
          (u : SobolevData (centeredCube z 1 hr)).1 := by
    rw [_P.besovSeminorm_eq z 1 hr
      ((u : SobolevData (centeredCube z 1 hr)).1) s hs01,
      _S.besovSeminorm_eq z 1 hr (1 - s) ht01
        ((u : SobolevData (centeredCube z 1 hr)).1)]
    simp only [Real.one_rpow]
  have hgrad :
      _P.besovGradSeminorm z 1 hr (u : SobolevData (centeredCube z 1 hr)) s 1 ≤
        _P.cssPow s 1 * (E.lam z 1 hr a z 1 s 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) := by
    simpa using _P.besov_grad_poincare_all_radii z 1 hr a s hs01
      (1 : ℝ≥0∞) le_rfl u
  have hnorm_nonneg :
      0 ≤ normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) := by
    unfold normalizedEnergyNorm
    exact Real.sqrt_nonneg _
  have hsqrt :
      Real.sqrt (normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) ^ 2) =
        normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
          (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnorm_nonneg]
  have hbesov_bound :
      _S.besovSeminorm z 1 hr (1 - s)
          (u : SobolevData (centeredCube z 1 hr)).1 ≤
        _P.C * _P.cssPow s 1 * (E.lam z 1 hr a z 1 s 1) ^ (-(1 / 2) : ℝ) *
          Real.sqrt (normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) ^ 2) := by
    rw [← hbesov]
    calc
      _ ≤ _P.C * _P.besovGradSeminorm z 1 hr
          (u : SobolevData (centeredCube z 1 hr)) s 1 :=
        _P.detach_all_radii z 1 hr s hs01 u
      _ ≤ _P.C * (_P.cssPow s 1 *
          (E.lam z 1 hr a z 1 s 1) ^ (-(1 / 2) : ℝ) *
            Real.sqrt (normalizedEnergyNorm a
              (centeredCube z 1 hr).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) ^ 2)) := by
        simpa [hsqrt] using
          (mul_le_mul_of_nonneg_left hgrad (le_of_lt _P.C_pos))
      _ = _ := by ring
  have hL' :
      ‖(u : SobolevData (centeredCube z 1 hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d))) ≤
        _P.C * (E.lam z 1 hr a z 1 1 1) ^ (-(1 / 2) : ℝ) *
          Real.sqrt (normalizedEnergyNorm a
            (centeredCube z 1 hr).isOpen.measurableSet
              (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) ^ 2) := by
    simpa [hsqrt] using hL
  have hLs : 0 < E.lam z 1 hr a z 1 s 1 :=
    E.lam_pos z 1 hr a z 1 s 1
  have hL1 : 0 < E.lam z 1 hr a z 1 1 1 :=
    E.lam_pos z 1 hr a z 1 1 1
  have hmono : E.lam z 1 hr a z 1 s 1 ≤ E.lam z 1 hr a z 1 1 1 :=
    E.lam_mono z 1 hr a z 1 1 s 1 (by linarith [hs.2])
  have hQ := _root_.SubdiffusiveProcess.EllipticRegularity.besov_h34_combine
    (Q := cubeFractionalSqNorm hd z 1 hr threeQuarterOrder
      (u : SobolevData (centeredCube z 1 hr)).1)
    (B := _S.besovSeminorm z 1 hr (1 - s)
      (u : SobolevData (centeredCube z 1 hr)).1)
    (L := ‖(u : SobolevData (centeredCube z 1 hr)).1‖ /
      Real.sqrt (volume.real (centeredCube z 1 hr : Set (SpatialCoordinates d))))
    (Eg := normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
      (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) ^ 2)
    (Ls := E.lam z 1 hr a z 1 s 1) (L1 := E.lam z 1 hr a z 1 1 1)
    (CS := _S.CBesov s) (CP := _P.C) (cs := _P.cssPow s 1)
    (le_of_lt (_S.CBesov_pos s hs)) (sq_nonneg _) 
    (_S.besovSeminorm_nonneg z 1 hr (1 - s)
      (u : SobolevData (centeredCube z 1 hr)).1)
    (by positivity) hLs hL1 hmono h3 hbesov_bound hL'
  have henergy_sq :
      normalizedEnergyNorm a (centeredCube z 1 hr).isOpen.measurableSet
          (sobolevGradient (u : SobolevData (centeredCube z 1 hr))) ^ 2 =
        sobolevCoefficientForm a (u : SobolevData (centeredCube z 1 hr))
          (u : SobolevData (centeredCube z 1 hr)) := by
    unfold normalizedEnergyNorm
    rw [hvol, div_one, Real.sq_sqrt
      (localGradientEnergy_nonneg a (centeredCube z 1 hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData (centeredCube z 1 hr)))),
      localGradientEnergy_domain_eq_sobolevCoefficientForm]
  constructor
  · exact hmem
  · simpa [henergy_sq] using hQ

theorem lane4_besov_h34_coercivity :
  ∀ (d : ℕ) (hd : 2 ≤ d) (E : in_J d) (_P : in_poincare d hd E)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd),
  ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∃ C : ℝ, 0 < C ∧
    ∀ (z : SpatialCoordinates d) (hr : (0 : ℝ) < 1)
      (a : PositiveCoefficient (centeredCube z 1 hr)),
      (∀ v : killedSobolevGraph (centeredCube z 1 hr),
        cubeFractionalL2Seminorm hd z 1 hr threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube z 1 hr)).1) < ⊤ ∧
        cubeFractionalSqNorm hd z 1 hr threeQuarterOrder
            (v : SobolevData (centeredCube z 1 hr)).1 ≤
          C * (E.lam z 1 hr a z 1 s 1)⁻¹ *
            sobolevCoefficientForm a (v : SobolevData (centeredCube z 1 hr))
              (v : SobolevData (centeredCube z 1 hr))) ∧
      (∀ v : meanZeroSobolevGraph (centeredCube z 1 hr),
        cubeFractionalL2Seminorm hd z 1 hr threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube z 1 hr)).1) < ⊤ ∧
        cubeFractionalSqNorm hd z 1 hr threeQuarterOrder
            (v : SobolevData (centeredCube z 1 hr)).1 ≤
          C * (E.lam z 1 hr a z 1 s 1)⁻¹ *
            sobolevCoefficientForm a (v : SobolevData (centeredCube z 1 hr))
              (v : SobolevData (centeredCube z 1 hr))) := by
  intro d hd E P S s hs
  let C : ℝ := S.CBesov s * P.C ^ 2 * (P.cssPow s 1 ^ 2 + 1)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have hcs : 0 < S.CBesov s := S.CBesov_pos s hs
    have hcP : 0 < P.C := P.C_pos
    have hcss : 0 < P.cssPow s 1 := P.cssPow_pos s 1
    have hlast : 0 < P.cssPow s 1 ^ 2 + 1 := by
      nlinarith [sq_nonneg (P.cssPow s 1)]
    exact mul_pos (mul_pos hcs (sq_pos_of_pos hcP)) hlast
  · intro z hr a
    constructor
    · intro v
      have hu : (v : SobolevData (centeredCube z 1 hr)) ∈
          weakSobolevGraph (centeredCube z 1 hr) :=
        killedSobolevGraph_le_weakSobolevGraph v.property
      let u : weakSobolevGraph (centeredCube z 1 hr) :=
        ⟨(v : SobolevData (centeredCube z 1 hr)), hu⟩
      have hp := P.poincare_killed z hr a v
      have h := aux_lane4_besov_h34_coercivity d hd E P S s hs z hr a u hp
      simpa [u, C] using h
    · intro v
      have hu : (v : SobolevData (centeredCube z 1 hr)) ∈
          weakSobolevGraph (centeredCube z 1 hr) :=
        (inf_le_left : meanZeroSobolevGraph (centeredCube z 1 hr) ≤
          weakSobolevGraph (centeredCube z 1 hr)) v.property
      let u : weakSobolevGraph (centeredCube z 1 hr) :=
        ⟨(v : SobolevData (centeredCube z 1 hr)), hu⟩
      have hp := P.poincare_meanZero z hr a v
      have h := aux_lane4_besov_h34_coercivity d hd E P S s hs z hr a u hp
      simpa [u, C] using h

end SubdiffusiveProcess.Paper
