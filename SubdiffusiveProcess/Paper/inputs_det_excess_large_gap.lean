module

public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorBoundary
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ComparisonDatumRetained
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ExcessDecayAdapter

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem aux_inputs_det_excess_large_gap_error_cap
    {Cerr epsilon : ℝ} (hCerr : 0 < Cerr)
    (hepsilon : epsilon ≤ 1) {err : ENNReal}
    (herr : err ≤ ENNReal.ofReal (Cerr * epsilon)) :
    err ≤ ENNReal.ofReal Cerr := by
  refine herr.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    Cerr * epsilon ≤ Cerr * 1 := mul_le_mul_of_nonneg_left hepsilon hCerr.le
    _ = Cerr := mul_one Cerr

theorem aux_inputs_det_excess_large_gap_real_cap
    {Cerr epsilon : ℝ} (hCerr : 0 < Cerr)
    (hepsilon : epsilon ≤ 1) {B : ℝ}
    (hB : B ≤ Cerr * epsilon) : B ≤ Cerr := by
  calc
    B ≤ Cerr * epsilon := hB
    _ ≤ Cerr * 1 := mul_le_mul_of_nonneg_left hepsilon hCerr.le
    _ = Cerr := mul_one Cerr

theorem aux_inputs_det_excess_large_gap_toReal_cap
    {err : ENNReal} {B : ℝ} (hB : 0 ≤ B)
    (herr : err ≤ ENNReal.ofReal B) : err.toReal ≤ B := by
  calc
    err.toReal ≤ (ENNReal.ofReal B).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top herr
    _ = B := ENNReal.toReal_ofReal hB

theorem aux_inputs_det_excess_large_gap_rhs_mono
    {C C' T₁ T₂ T₃ T₄ : ℝ} {p : Prop} [Decidable p]
    (hCC : C ≤ C') (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hT₃ : 0 ≤ T₃) (hT₄ : 0 ≤ T₄) :
    C * T₁ + C * T₂ + C * T₃ + (if p then C * T₄ else 0) ≤
      C' * T₁ + C' * T₂ + C' * T₃ + (if p then C' * T₄ else 0) := by
  have h₁ : C * T₁ ≤ C' * T₁ := mul_le_mul_of_nonneg_right hCC hT₁
  have h₂ : C * T₂ ≤ C' * T₂ := mul_le_mul_of_nonneg_right hCC hT₂
  have h₃ : C * T₃ ≤ C' * T₃ := mul_le_mul_of_nonneg_right hCC hT₃
  have h₄ : C * T₄ ≤ C' * T₄ := mul_le_mul_of_nonneg_right hCC hT₄
  by_cases hp : p
  · simp [hp]
    linarith
  · simp [hp]
    linarith

theorem aux_inputs_det_excess_large_gap_remainder_bound
    (d : ℕ) [NeZero d] {Csch : ℝ} (hCsch : 0 ≤ Csch) (k : ℕ) :
    Section6ExcessDecay.oneStepRemainderConst d Csch k ≤
      (81 * Section6ExcessDecay.taylorConst d * Csch + 1) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
  have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
    Real.rpow_nonneg (by norm_num) _
  have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      positivity
    simpa using h0
  have h81 : (0 : ℝ) ≤ 81 * Section6ExcessDecay.taylorConst d * Csch :=
    mul_nonneg (mul_nonneg (by norm_num)
      (Section6ExcessDecay.taylorConst_nonneg d)) hCsch
  have hleft : 81 * Section6ExcessDecay.taylorConst d * Csch *
        ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤
      81 * Section6ExcessDecay.taylorConst d * Csch *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
    mul_le_mul_of_nonneg_left
      (le_trans Section6ExcessDecay.three_zpow_rpow_half_le_one hb1) h81
  have hright : (3 : ℝ) ^ (k : ℤ) *
        Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) ≤
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
    have ht0 : (0 : ℝ) < (3 : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have htz : (3 : ℝ) ^ (k : ℤ) = (3 : ℝ) ^ (k : ℝ) := by
      rw [← Real.rpow_intCast (3 : ℝ) (k : ℤ)]
      norm_num
    have hsq : Real.sqrt (((3 : ℝ) ^ (k : ℝ)) ^ d) =
        ((3 : ℝ) ^ (k : ℝ)) ^ ((d : ℝ) / 2) :=
      Section6ExcessDecay.sqrt_pow_eq_rpow_half ht0.le d
    have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) ≤
        Real.sqrt (((3 : ℝ) ^ (k : ℝ)) ^ d) := by
      refine Real.sqrt_le_sqrt ?_
      rw [← htz]
      exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
        (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
    have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * (k : ℝ)) =
        (3 : ℝ) ^ (k : ℝ) * ((3 : ℝ) ^ (k : ℝ)) ^ ((d : ℝ) / 2) :=
      Section6ExcessDecay.three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
    rw [hsplit, htz]
    exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
  rw [Section6ExcessDecay.oneStepRemainderConst]
  linarith

/-- The boundary comparison of the harmonic replacement at ONE tuple (window `x`, anchor `z`, coefficient
`a` with its anchored certificate and reference `a0`, solution `u`, datum `h`, force `g`), with constant `CAb`,
for every admissible window centre `y`.  This is the single use that the large-gap excess estimate makes of the
boundary clause of `l.harmonic.approximation.good.scales.GMC`; the cutoff-field instance is supplied by
`inputs_deterministic_boundary`. -/
def aux_inputs_det_excess_large_gap_Cmp (d : ℕ) [NeZero d] (CAb s : ℝ) (m n : ℕ) (z x : Vec d)
    (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun y => a (y + z))) (a0 : ℝ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d) : Prop :=
  let err : ENNReal :=
    paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0;
  ∀ y ∈ cube d m,
            truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
            translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
            ∀ uD : H1Function (translatedCube d (n - 2) y),
              (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
            (∃ v : H1Function (translatedCube d (n - 2) y),
              IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
            (∀ v v' : H1Function (translatedCube d (n - 2) y),
              (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                  HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
              (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                  HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
              v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
                v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
            ∀ (v : H1Function (translatedCube d (n - 2) y)),
              IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
              normalizedL2On (truncatedCube d m (n - 4) x)
                  (fun q => u.toFun q - v.toFun q) ≤
                CAb * s ^ (-3 / 2 : ℝ) * err.toReal *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  CAb * s ^ (-15 / 2 : ℝ) *
                    (a0)⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0)

theorem inputs_det_excess_large_gap (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cerr : ℝ) (hCerr : 0 < Cerr)
    (CAb : ℝ) (hCAb : 0 < CAb) :
    (∃ C : ℝ, 0 < C ∧
      3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ C ∧
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ epsilon ∈ Set.Ioc (0 : ℝ) 1, ∀ k : ℕ, 6 ≤ k → 0 < k →
      ∀ m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
      ∀ a0 : ℝ, 0 < a0 →
      let err : ENNReal :=
        paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0;
      err ≤ ENNReal.ofReal (Cerr * epsilon) →
      Homogenization.Book.Ch02.HomogenizationErrorOnCube
          (originCube d ((n : ℤ) + 2)) (s / 6) .infinity (.finite 2)
          data.toTriadicCoeffFamily (Homogenization.scalarMatrix (d := d) a0) ≤
        Cerr * epsilon →
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn a (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        aux_inputs_det_excess_large_gap_Cmp d CAb s m n z x a data a0 u h g →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
              excess n (truncatedCube d m n x) u.toFun +
            C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
              err.toReal *
              (Real.sqrt (vecNormSq ell.slope) +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) *
                    Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                else 0)) +
            C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (a0)⁻¹ * (3 : ℝ) ^ (s * n) *
              (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (3 : ℝ) ^ ((n : ℝ) / 2) *
                holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
            else 0)) := by
  haveI : NeZero d := inferInstance
  have hd1 : 1 ≤ d := by omega
  have hCAbpos : 0 < CAb := hCAb
  obtain ⟨Csch, hCsch, hBoundaryStep⟩ :=
    Section6ExcessDecay.exists_excess_oneStep_boundary_anchor d (by omega)
  let CschI := Section6Schauder.schauderInteriorConst d
  let Cstep := max CschI Csch
  have hCstep : 0 ≤ Cstep := by
    dsimp [Cstep, CschI]
    exact le_max_of_le_right hCsch
  let C := Section6ExcessDecay.anchorBoundaryConst d CAb Cerr Cstep
  have hC : 0 < C :=
    Section6ExcessDecay.anchorBoundaryConst_pos d hCAbpos.le hCerr.le hCstep
  have hCbase : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ C := by
    exact Section6ExcessDecay.anchorBoundaryConst_crude_le d hCAbpos.le hCerr.le hCstep
  refine ⟨C, hC, hCbase, ?_⟩
  intro s hs hs4 epsilon hepsilon k hk6 hkpos m n hkn hnm x hx z hz hxz a data a0 ha0
    err hErr hHom u h g hDir hSob hHolder hcmp ell hell
  have heps : epsilon ≤ 1 := hepsilon.2
  have herrCap : err ≤ ENNReal.ofReal Cerr :=
    aux_inputs_det_excess_large_gap_error_cap hCerr heps hErr
  have hMemHW : MemFractionalOn (cube d m) s h.grad :=
    Section6ExcessDecay.memFractionalOn_cube_of_memHolder hd1 hs hs4 hHolder
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
  have hstep6 := Section6ExcessDecay.normalizedL2On_sub_average_le
    (m := (m : ℤ)) (n := (n : ℤ)) (x := x) hx (by omega) hu_n hell
  set E := excess (n : ℤ) (truncatedCube d m n x) u.toFun
  set Err := err.toReal
  set Sl := Real.sqrt (vecNormSq ell.slope)
  set Ah := Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
  set J := if BoundaryTouches (truncatedCube d m n x) (cube d m) then
      s ^ (-3 / 2 : ℝ) * Ah else 0
  set Fg := (fractionalSeminormOn (truncatedCube d m n x) s g).toReal
  set Hh := holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
  set Tinv := (a0)⁻¹
  set bb := (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
  set pk := (3 : ℝ) ^ (-(k : ℝ) / 2)
  set ss := s ^ (-3 / 2 : ℝ)
  set s15 := s ^ (-15 / 2 : ℝ)
  set qn := (3 : ℝ) ^ (s * n)
  set XG := if BoundaryTouches (truncatedCube d m n x) (cube d m) then
      C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (3 : ℝ) ^ ((n : ℝ) / 2) * holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
    else 0
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Section6ExcessDecay.excess_nonneg _ _ _
  have hErrn : 0 ≤ Err := by dsimp [Err]; exact ENNReal.toReal_nonneg
  have hSl : 0 ≤ Sl := by dsimp [Sl]; exact Real.sqrt_nonneg _
  have hAh : 0 ≤ Ah := by dsimp [Ah]; exact Real.sqrt_nonneg _
  have hFg : 0 ≤ Fg := by dsimp [Fg]; exact ENNReal.toReal_nonneg
  have hTinv : 0 ≤ Tinv := by dsimp [Tinv]; exact inv_nonneg.mpr ha0.le
  have hHh : 0 ≤ Hh := by
    dsimp [Hh]
    exact Section6ExcessDecay.holderSeminormOn_nonneg
      (Section6ExcessDecay.memHolder_mono hHolder (truncatedCube_subset_cube d m n x))
  have hJ : 0 ≤ J := by
    dsimp [J]
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg hs.le _) hAh
    · exact le_rfl
  have heps0 : 0 ≤ epsilon := hepsilon.1.le
  have hbb : 0 ≤ bb := by dsimp [bb]; positivity
  have hpk : 0 ≤ pk := by dsimp [pk]; positivity
  have hss : 0 ≤ ss := by dsimp [ss]; positivity
  have hs15 : 0 ≤ s15 := by dsimp [s15]; positivity
  have hqn : 0 ≤ qn := by dsimp [qn]; positivity
  have hcap : Err ≤ Cerr * epsilon := by
    dsimp [Err]
    exact aux_inputs_det_excess_large_gap_toReal_cap
      (mul_nonneg hCerr.le heps0) hErr
  obtain ⟨y, hy, hy1, hy2⟩ :=
    Section6ExcessDecay.exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
  have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
    hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
  have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
    Section6Schauder.isOpen_translatedCube d _ y
  have huDval : ∀ q, (u.restrict hYopen hYsub).toFun q = u.toFun q := fun _ => rfl
  have huDgrad : ∀ q, (u.restrict hYopen hYsub).grad q = u.grad q := fun _ => rfl
  rcases hcmp y hy hy1 hy2 (u.restrict hYopen hYsub) huDval huDgrad with
    ⟨⟨v, hvharm, hvzt⟩, huniq, hbound⟩
  have hDapprox := hbound v hvharm hvzt
  have hHolderTrunc : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
    Section6ExcessDecay.memHolder_mono hHolder (truncatedCube_subset_cube d m n x)
  have hstep8 := Section6ExcessDecay.holderLeg_le
    (m := (m : ℤ)) (j := (n : ℤ)) (x := x) (f := h.grad) (s := s)
    hd1 hx hs hs4 hHolderTrunc
  simp only [Int.cast_natCast] at hstep8
  set D := normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
    (fun q => u.toFun q - v.toFun q)
  set Fh := (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal
  have hDapprox' : D ≤
      CAb * ss * Err *
        (normalizedL2On (truncatedCube d m n x)
          (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
          (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
            s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
      CAb * s15 * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
      (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0) := by
    simpa [D, Fg, Fh, Err, Tinv, ss, s15] using hDapprox
  have hNbound : (3 : ℝ) ^ (-(n : ℤ)) *
        normalizedL2On (truncatedCube d m n x)
          (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) ≤
      E + Real.sqrt (d : ℝ) / 2 * Sl := by
    simpa [E, Sl] using hstep6
  have hfront : (3 : ℝ) ^ (-(n : ℤ)) *
        (3 : ℝ) ^ ((1 + s) * (n : ℝ)) = (3 : ℝ) ^ (s * (n : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have h3nn : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ) = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
  have hJeq : (3 : ℝ) ^ (-(n : ℤ)) *
        (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
          s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0) = J := by
    dsimp [J]
    split_ifs
    · calc
        (3 : ℝ) ^ (-(n : ℤ)) * (s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ (n : ℕ) * Ah)
            = ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ)) *
                (s ^ (-3 / 2 : ℝ) * Ah) := by ring
        _ = s ^ (-3 / 2 : ℝ) * Ah := by rw [h3nn, one_mul]
    · simp
  have hspow1 : s ^ (-4 : ℝ) * Real.sqrt s = s ^ (-7 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
    norm_num
  have hspow2 : s ^ (-7 / 2 : ℝ) * Real.sqrt s = s ^ (-3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
    norm_num
  have hsource1 : s ^ (-7 / 2 : ℝ) *
        ((3 : ℝ) ^ (-(n : ℤ)) *
          ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)) ≤
      Section6ExcessDecay.fractionalHolderConst d * s ^ (-3 : ℝ) *
        (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
    have hmul := mul_le_mul_of_nonneg_right hstep8 (Real.sqrt_nonneg s)
    calc
      s ^ (-7 / 2 : ℝ) *
          ((3 : ℝ) ^ (-(n : ℤ)) *
            ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh))
          = s ^ (-4 : ℝ) *
              ((3 : ℝ) ^ (-(n : ℤ)) *
                ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)) * Real.sqrt s := by
              rw [← hspow1]
              ring
      _ ≤ (Section6ExcessDecay.fractionalHolderConst d * s ^ (-7 / 2 : ℝ) *
            (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) * Real.sqrt s := hmul
      _ = Section6ExcessDecay.fractionalHolderConst d * s ^ (-3 : ℝ) *
            (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
              calc
                _ = Section6ExcessDecay.fractionalHolderConst d *
                    (s ^ (-7 / 2 : ℝ) * Real.sqrt s) *
                    (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by ring
                _ = _ := by rw [hspow2]
  set XHsrc := if BoundaryTouches (truncatedCube d m n x) (cube d m) then
      CAb * Section6ExcessDecay.fractionalHolderConst d * s ^ (-3 : ℝ) *
        (3 : ℝ) ^ ((n : ℝ) / 2) * Hh else 0
  have hXHolder : (3 : ℝ) ^ (-(n : ℤ)) *
        (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
          CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0)
      ≤ XHsrc := by
    by_cases hbd : BoundaryTouches (truncatedCube d m n x) (cube d m)
    · simp only [if_pos hbd, XHsrc]
      calc
        (3 : ℝ) ^ (-(n : ℤ)) *
            (CAb * s ^ (-7 / 2 : ℝ) *
              (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
            = CAb * s ^ (-7 / 2 : ℝ) *
                ((3 : ℝ) ^ (-(n : ℤ)) *
                  ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)) := by ring
        _ = CAb * (s ^ (-7 / 2 : ℝ) *
              ((3 : ℝ) ^ (-(n : ℤ)) *
                ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh))) := by ring
        _ ≤ CAb * (Section6ExcessDecay.fractionalHolderConst d *
              s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) :=
            mul_le_mul_of_nonneg_left hsource1 hCAbpos.le
        _ = CAb * Section6ExcessDecay.fractionalHolderConst d *
              s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by ring
    · simp [hbd, XHsrc]
  have hDweighted : (3 : ℝ) ^ (-(n : ℤ)) * D ≤
      CAb * ss * Err * E + CAb * ss * Err * (Real.sqrt (d : ℝ) / 2 * Sl) +
        CAb * ss * Err * J + CAb * s15 * Tinv * qn * Fg + XHsrc := by
    have hbase := mul_le_mul_of_nonneg_left hDapprox'
      (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(n : ℤ)))
    have hcoeff : 0 ≤ CAb * ss * Err :=
      mul_nonneg (mul_nonneg hCAbpos.le hss) hErrn
    have hmean := mul_le_mul_of_nonneg_left hNbound hcoeff
    have hsplit :
        (3 : ℝ) ^ (-(n : ℤ)) *
          (CAb * ss * Err *
              (normalizedL2On (truncatedCube d m n x)
                (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
            CAb * s15 * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0))
          =
        CAb * ss * Err *
            ((3 : ℝ) ^ (-(n : ℤ)) *
              normalizedL2On (truncatedCube d m n x)
                (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun)) +
          CAb * ss * Err *
            ((3 : ℝ) ^ (-(n : ℤ)) *
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
          CAb * s15 * Tinv *
            ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg +
          (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0) := by ring
    have hmeanSplit : CAb * ss * Err *
          ((3 : ℝ) ^ (-(n : ℤ)) *
            normalizedL2On (truncatedCube d m n x)
              (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun)) ≤
        CAb * ss * Err * E +
          CAb * ss * Err * (Real.sqrt (d : ℝ) / 2 * Sl) := by
      calc
        _ ≤ CAb * ss * Err * (E + Real.sqrt (d : ℝ) / 2 * Sl) :=
          mul_le_mul_of_nonneg_left hNbound hcoeff
        _ = _ := by ring
    calc
      (3 : ℝ) ^ (-(n : ℤ)) * D
          ≤ (3 : ℝ) ^ (-(n : ℤ)) *
              (CAb * ss * Err *
                  (normalizedL2On (truncatedCube d m n x)
                    (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
                CAb * s15 * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0)) := hbase
      _ = CAb * ss * Err *
            ((3 : ℝ) ^ (-(n : ℤ)) *
              normalizedL2On (truncatedCube d m n x)
                (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun)) +
          CAb * ss * Err * J + CAb * s15 * Tinv * qn * Fg +
            (3 : ℝ) ^ (-(n : ℤ)) *
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                CAb * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0) := by
            rw [hsplit, hJeq, hfront]
      _ ≤ CAb * ss * Err * E +
            CAb * ss * Err * (Real.sqrt (d : ℝ) / 2 * Sl) +
            CAb * ss * Err * J + CAb * s15 * Tinv * qn * Fg + XHsrc := by
              calc
                _ = (CAb * ss * Err *
                      ((3 : ℝ) ^ (-(n : ℤ)) *
                        normalizedL2On (truncatedCube d m n x)
                          (fun q => u.toFun q -
                            averageOn (truncatedCube d m n x) u.toFun)) +
                    CAb * ss * Err * J) +
                    (CAb * s15 * Tinv * qn * Fg +
                      (3 : ℝ) ^ (-(n : ℤ)) *
                        (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                          CAb * s ^ (-7 / 2 : ℝ) *
                            (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0)) := by ring
                _ ≤ (CAb * ss * Err * E +
                      CAb * ss * Err * (Real.sqrt (d : ℝ) / 2 * Sl) +
                    CAb * ss * Err * J) +
                      (CAb * s15 * Tinv * qn * Fg + XHsrc) := by
                      exact add_le_add (add_le_add hmeanSplit le_rfl)
                        (add_le_add le_rfl hXHolder)
                _ = _ := by ring
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    unfold normalizedL2On
    exact Real.sqrt_nonneg _
  have hDweightedNonneg : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) * D :=
    mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(n : ℤ))) hDnonneg
  have hfactor : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = pk := by
    rw [Section6ExcessDecay.three_zpow_rpow_half_eq]
    push_cast
    dsimp [pk]
  let Kc := Section6ExcessDecay.oneStepContractionConst d * Cstep *
    ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
  let Kr := Section6ExcessDecay.oneStepRemainderConst d Cstep k
  have hfactor0 : 0 ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
    Section6ExcessDecay.three_zpow_rpow_half_nonneg (-(k : ℤ))
  have hK0 : 0 ≤ Section6ExcessDecay.oneStepContractionConst d :=
    Section6ExcessDecay.oneStepContractionConst_nonneg d
  have hKcoeffMono : ∀ c0 : ℝ, c0 ≤ Cstep →
      Section6ExcessDecay.oneStepContractionConst d * c0 *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤ Kc := by
    intro c0 hc0
    calc
      Section6ExcessDecay.oneStepContractionConst d * c0 *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤
        (Section6ExcessDecay.oneStepContractionConst d * Cstep) *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc0 hK0) hfactor0
      _ = Kc := by rfl
  have hKrMono : ∀ c0 : ℝ, c0 ≤ Cstep →
      Section6ExcessDecay.oneStepRemainderConst d c0 k ≤ Kr := by
    intro c0 hc0
    change Section6ExcessDecay.oneStepRemainderConst d c0 k ≤
      Section6ExcessDecay.oneStepRemainderConst d Cstep k
    unfold Section6ExcessDecay.oneStepRemainderConst
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc0
          (mul_nonneg (by norm_num) (Section6ExcessDecay.taylorConst_nonneg d)))
        hfactor0
    · exact le_rfl
  have hKcBase : Section6ExcessDecay.oneStepContractionConst d * Cstep ≤ C :=
    Section6ExcessDecay.anchorBoundaryConst_contraction_le d hCAbpos.le hCerr.le hCstep
  have hKcle : Kc ≤ C * pk := by
    dsimp [Kc]
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right hKcBase hpk
  have hKr0 : 0 ≤ Kr := by
    dsimp [Kr]
    exact Section6ExcessDecay.oneStepRemainderConst_nonneg d hCstep k
  have hKrBound : Kr ≤
      (81 * Section6ExcessDecay.taylorConst d * Cstep + 1) * bb := by
    dsimp [Kr, bb]
    exact aux_inputs_det_excess_large_gap_remainder_bound d hCstep k
  let fac := 81 * Section6ExcessDecay.taylorConst d * Cstep + 1
  let budget := Cerr + 1 + Real.sqrt (d : ℝ) / 2 +
    Section6ExcessDecay.fractionalHolderConst d
  let bracket := CAb * budget + Section6ExcessDecay.correctorLegConst d
  have hfac0 : 0 ≤ fac := by
    dsimp [fac]
    have ht := Section6ExcessDecay.taylorConst_nonneg d
    positivity
  have hfh0 : 0 ≤ Section6ExcessDecay.fractionalHolderConst d :=
    Section6ExcessDecay.fractionalHolderConst_nonneg d
  have hcorrector0 : 0 ≤ Section6ExcessDecay.correctorLegConst d :=
    Section6ExcessDecay.correctorLegConst_nonneg d
  have hbudget0 : 0 ≤ budget := by
    dsimp [budget]
    have hsqr := Real.sqrt_nonneg (d : ℝ)
    linarith [hCerr.le, hfh0]
  have hbracket0 : 0 ≤ bracket := by
    dsimp [bracket]
    exact add_nonneg (mul_nonneg hCAbpos.le hbudget0) hcorrector0
  have hCrem : fac * bracket ≤ C := by
    simpa [fac, bracket, budget, C] using
      (Section6ExcessDecay.anchorBoundaryConst_remainder_le d hCstep)
  have hbudgetB : ∀ c : ℝ, 0 ≤ c → c ≤ bracket → Kr * c ≤ C * bb := by
    intro c hc0 hcle
    have hfacbound : fac * c ≤ fac * bracket :=
      mul_le_mul_of_nonneg_left hcle hfac0
    have h1 : Kr * c ≤ (fac * bb) * c :=
      mul_le_mul_of_nonneg_right hKrBound hc0
    have h2 : (fac * bb) * c = (fac * c) * bb := by ring
    calc
      Kr * c ≤ (fac * bb) * c := h1
      _ = (fac * c) * bb := h2
      _ ≤ (fac * bracket) * bb := mul_le_mul_of_nonneg_right hfacbound hbb
      _ ≤ C * bb := mul_le_mul_of_nonneg_right hCrem hbb
  have hroot0 : 0 ≤ Real.sqrt (d : ℝ) / 2 := by positivity
  have hbCerr : Cerr ≤ budget := by
    dsimp [budget]
    linarith [hfh0, Real.sqrt_nonneg (d : ℝ)]
  have hbOne : (1 : ℝ) ≤ budget := by
    dsimp [budget]
    linarith [hCerr.le, hfh0, Real.sqrt_nonneg (d : ℝ)]
  have hbRoot : Real.sqrt (d : ℝ) / 2 ≤ budget := by
    dsimp [budget]
    linarith [hCerr.le, hfh0, Real.sqrt_nonneg (d : ℝ)]
  have hbFH : Section6ExcessDecay.fractionalHolderConst d ≤ budget := by
    dsimp [budget]
    linarith [hCerr.le, Real.sqrt_nonneg (d : ℝ)]
  have hBudgetC : ∀ c : ℝ, 0 ≤ c → c ≤ budget → CAb * c ≤ bracket := by
    intro c hc hcb
    calc
      CAb * c ≤ CAb * budget := mul_le_mul_of_nonneg_left hcb hCAbpos.le
      _ ≤ bracket := by dsimp [bracket]; exact le_add_of_nonneg_right hcorrector0
  have hcoeffCerr : 0 ≤ CAb * Cerr := mul_nonneg hCAbpos.le hCerr.le
  have hcoeffRoot : 0 ≤ CAb * (Real.sqrt (d : ℝ) / 2) :=
    mul_nonneg hCAbpos.le hroot0
  have hcoeffOne : 0 ≤ CAb := hCAbpos.le
  have hcoeffFH : 0 ≤ CAb * Section6ExcessDecay.fractionalHolderConst d :=
    mul_nonneg hCAbpos.le hfh0
  have hcoeffAgg : 0 ≤ CAb * Section6ExcessDecay.fractionalHolderConst d +
      Section6ExcessDecay.correctorLegConst d := add_nonneg hcoeffFH hcorrector0
  have hboundCerr : CAb * Cerr ≤ bracket := hBudgetC Cerr hCerr.le hbCerr
  have hboundRoot : CAb * (Real.sqrt (d : ℝ) / 2) ≤ bracket :=
    hBudgetC _ hroot0 hbRoot
  have hboundOne : CAb ≤ bracket := by simpa using hBudgetC 1 zero_le_one hbOne
  have hboundFH : CAb * Section6ExcessDecay.fractionalHolderConst d ≤ bracket :=
    hBudgetC _ hfh0 hbFH
  have hboundAgg : CAb * Section6ExcessDecay.fractionalHolderConst d +
      Section6ExcessDecay.correctorLegConst d ≤ bracket := by
    dsimp [bracket]
    exact add_le_add (mul_le_mul_of_nonneg_left hbFH hCAbpos.le) le_rfl
  have hb1 : Kr * CAb * Cerr ≤ C * bb := by
    calc
      Kr * CAb * Cerr = Kr * (CAb * Cerr) := by ring
      _ ≤ C * bb := hbudgetB _ hcoeffCerr hboundCerr
  have hb2 : Kr * CAb * (Real.sqrt (d : ℝ) / 2) ≤ C * bb := by
    calc
      Kr * CAb * (Real.sqrt (d : ℝ) / 2) =
          Kr * (CAb * (Real.sqrt (d : ℝ) / 2)) := by ring
      _ ≤ C * bb := hbudgetB _ hcoeffRoot hboundRoot
  have hb3 : Kr * CAb ≤ C * bb := hbudgetB _ hcoeffOne hboundOne
  by_cases hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m
  · obtain ⟨v', K, hv'ae, hv'mem, hK0', hint, hgradv, hholK, hschauder⟩ :=
      Section6Schauder.exists_gradientHolder_of_weaklyHarmonic (d := d)
        (m := (m : ℤ)) (n := (n : ℤ)) (x := x) (y := y) (by omega) hx
        (by omega) hgate hy1 hvharm
    have hv'4 : MemLp v' 2
        (volume.restrict (truncatedCube d m ((n : ℤ) - 4) x)) := hv'mem.restrict _
    have honeI := Section6ExcessDecay.excess_oneStep_of_schauder
      (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k) (Kh := 0)
      hk6 hx (by omega) hu_n hv'4 hK0'
      (Section6Schauder.schauderInteriorConst_nonneg d) hint hgradv hholK hschauder
    have hDeq : normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
          (fun p => u.toFun p - v' p) =
        normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
          (fun q => u.toFun q - v.toFun q) := by
      refine Section6ExcessDecay.normalizedL2On_congr_ae ?_
      have hres : v' =ᵐ[volume.restrict (truncatedCube d m ((n : ℤ) - 4) x)] v.toFun :=
        hv'ae.filter_mono (ae_mono (Measure.restrict_mono hy1 le_rfl))
      filter_upwards [hres] with p hp
      rw [hp]
    rw [hDeq, mul_zero, add_zero] at honeI
    let KI := Section6ExcessDecay.oneStepContractionConst d * CschI *
      ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
    let KRi := Section6ExcessDecay.oneStepRemainderConst d CschI k
    have honeI' : excess ((n : ℤ) - (k : ℤ))
          (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun ≤
        KI * E + KRi * ((3 : ℝ) ^ (-(n : ℤ)) * D) := by
      simpa [KI, KRi, E, D] using honeI
    have hKIle : KI ≤ Kc := by
      dsimp [KI, Kc]
      exact hKcoeffMono CschI (le_max_left _ _)
    have hKRile : KRi ≤ Kr := by
      dsimp [KRi]
      exact hKrMono CschI (le_max_left _ _)
    have hD0 : 0 ≤ D := by
      dsimp [D]
      unfold normalizedL2On
      exact Real.sqrt_nonneg _
    have hDw0 : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) * D :=
      mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(n : ℤ))) hD0
    have hone : excess ((n : ℤ) - (k : ℤ))
          (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun ≤
        Kc * E + Kr * ((3 : ℝ) ^ (-(n : ℤ)) * D) := by
      calc
        _ ≤ KI * E + KRi * ((3 : ℝ) ^ (-(n : ℤ)) * D) := honeI'
        _ ≤ Kc * E + Kr * ((3 : ℝ) ^ (-(n : ℤ)) * D) :=
          add_le_add (mul_le_mul_of_nonneg_right hKIle hE)
            (mul_le_mul_of_nonneg_right hKRile hDw0)
    let XH := XHsrc
    have hXHbound : Kr * XH ≤ XG := by
      by_cases hbd : BoundaryTouches (truncatedCube d m n x) (cube d m)
      · have hcoef := hbudgetB (CAb * Section6ExcessDecay.fractionalHolderConst d)
          hcoeffFH hboundFH
        have hfac : 0 ≤ s ^ (-3 : ℝ) *
            (3 : ℝ) ^ ((n : ℝ) / 2) * Hh :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg (by norm_num) _)) hHh
        have htmp : Kr * (CAb * Section6ExcessDecay.fractionalHolderConst d *
              s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) ≤
            C * s ^ (-3 : ℝ) * bb * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
          calc
            _ = (Kr * (CAb * Section6ExcessDecay.fractionalHolderConst d)) *
                  (s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) := by ring
            _ ≤ (C * bb) *
                  (s ^ (-3 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) :=
              mul_le_mul_of_nonneg_right hcoef hfac
            _ = _ := by ring
        simpa [XH, XHsrc, XG, bb, Hh, hbd] using htmp
      · simp [XH, XHsrc, XG, hbd]
    have hcombine := Section6ExcessDecay.excessDecayCombine
      (E := E) (Err := Err) (Sl := Sl) (Fg := Fg) (Tinv := Tinv) (J := J)
      (eps := epsilon) (XH := XH) (XG := XG) (Kc := Kc) (Kr := Kr)
      (CA := CAb) (CB := Cerr) (Cc := C) (bb := bb) (ss := ss) (s15 := s15)
      (pk := pk) (qn := qn) (r2 := Real.sqrt (d : ℝ) / 2)
      hE hErrn hSl hFg hTinv hJ heps0 hss hs15 hqn hKr0 hCAbpos.le
      hone hDweighted hcap hKcle hb1 hb2 hb3 hXHbound
    simpa [E, Err, Sl, Fg, Tinv, J, bb, ss, s15, pk, qn, XG] using hcombine
  · have hbd : BoundaryTouches (truncatedCube d m n x) (cube d m) :=
      Section6ExcessDecay.boundaryTouches_of_not_translatedCube_subset
        hx (by omega) hgate
    have hdat : MemH10 (openCubeSet (originCube d m))
        (fun p => u.toFun p - h.toFun p) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.memH10_sub_physical_of_hasZeroTraceDifferenceOn
        hDir.1 (fun _ => rfl)
    have hvu : MemH10 (translatedCube d ((n : ℤ) - 2) y)
        (fun p => v.toFun p - u.toFun p) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.memH10_sub_physical_of_hasZeroTraceDifferenceOn
        hvzt huDval
    have hone := hBoundaryStep m n k hk6 (by omega) x y hx hy1 hy2 hgate
      u h hdat hHolderTrunc v hvharm hvu
    let Corr := Section6ExcessDecay.correctorLegConst d *
      (3 : ℝ) ^ ((n : ℝ) / 2) * Hh
    let Ds := (3 : ℝ) ^ (-(n : ℤ)) * D + Corr
    let XH := XHsrc + Corr
    let KB := Section6ExcessDecay.oneStepContractionConst d * Csch *
      ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
    let KRB := Section6ExcessDecay.oneStepRemainderConst d Csch k
    have honeB' : excess ((n : ℤ) - (k : ℤ))
          (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun ≤
        KB * E + KRB * ((3 : ℝ) ^ (-(n : ℤ)) * D) + KRB * Corr := by
      simpa [KB, KRB, E, D, Corr, Hh] using hone
    have hKBle : KB ≤ Kc := by
      dsimp [KB, Kc]
      exact hKcoeffMono Csch (le_max_right _ _)
    have hKRBle : KRB ≤ Kr := by
      dsimp [KRB]
      exact hKrMono Csch (le_max_right _ _)
    have hCorr0 : 0 ≤ Corr := by
      dsimp [Corr]
      exact mul_nonneg
        (mul_nonneg (Section6ExcessDecay.correctorLegConst_nonneg d)
          (Real.rpow_nonneg (by norm_num) _)) hHh
    have hDwCorr0 : 0 ≤ (3 : ℝ) ^ (-(n : ℤ)) * D + Corr :=
      add_nonneg hDweightedNonneg hCorr0
    have honeB : excess ((n : ℤ) - (k : ℤ))
          (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun ≤
        Kc * E + Kr * Ds := by
      calc
        _ ≤ KB * E + KRB * ((3 : ℝ) ^ (-(n : ℤ)) * D) + KRB * Corr := honeB'
        _ = KB * E + KRB * ((3 : ℝ) ^ (-(n : ℤ)) * D + Corr) := by ring
        _ ≤ Kc * E + Kr * ((3 : ℝ) ^ (-(n : ℤ)) * D + Corr) :=
          add_le_add (mul_le_mul_of_nonneg_right hKBle hE)
            (mul_le_mul_of_nonneg_right hKRBle hDwCorr0)
    have hDs : Ds ≤ CAb * ss * Err * E +
        CAb * ss * Err * (Real.sqrt (d : ℝ) / 2 * Sl) + CAb * ss * Err * J +
        CAb * s15 * Tinv * qn * Fg + XH := by
      dsimp [Ds, XH]
      calc
        (3 : ℝ) ^ (-(n : ℤ)) * D + Corr ≤
            CAb * ss * Err * E + CAb * ss * Err * (Real.sqrt (d : ℝ) / 2 * Sl) +
            CAb * ss * Err * J + CAb * s15 * Tinv * qn * Fg + XHsrc + Corr :=
          add_le_add hDweighted le_rfl
        _ = _ := by ring
    have hbd : BoundaryTouches (truncatedCube d m n x) (cube d m) :=
      Section6ExcessDecay.boundaryTouches_of_not_translatedCube_subset
        hx (by omega) hgate
    have hS3pos : 0 < s ^ (3 : ℕ) := pow_pos hs 3
    have hS3le : s ^ (3 : ℕ) ≤ 1 := by
      calc
        s ^ (3 : ℕ) ≤ (1 / 4 : ℝ) ^ (3 : ℕ) :=
          pow_le_pow_left₀ hs.le hs4 3
        _ ≤ 1 := by norm_num
    have hSneg3 : s ^ (-3 : ℝ) = (s ^ (3 : ℕ))⁻¹ := by
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      rfl
    have hS3ge : 1 ≤ s ^ (-3 : ℝ) := by
      rw [hSneg3]
      exact (one_le_inv₀ hS3pos).2 hS3le
    have hS3nonneg : 0 ≤ s ^ (-3 : ℝ) := Real.rpow_nonneg hs.le _
    have hAggCoeff := hbudgetB
      (CAb * Section6ExcessDecay.fractionalHolderConst d +
        Section6ExcessDecay.correctorLegConst d) hcoeffAgg hboundAgg
    have hSourceCorrCoeff : CAb * Section6ExcessDecay.fractionalHolderConst d *
          s ^ (-3 : ℝ) + Section6ExcessDecay.correctorLegConst d ≤
        (CAb * Section6ExcessDecay.fractionalHolderConst d +
          Section6ExcessDecay.correctorLegConst d) * s ^ (-3 : ℝ) := by
      calc
        _ ≤ CAb * Section6ExcessDecay.fractionalHolderConst d *
              s ^ (-3 : ℝ) +
            Section6ExcessDecay.correctorLegConst d * s ^ (-3 : ℝ) :=
          add_le_add le_rfl (by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hS3ge hcorrector0))
        _ = _ := by ring_nf
    have hCoeffFinal : Kr *
          (CAb * Section6ExcessDecay.fractionalHolderConst d * s ^ (-3 : ℝ) +
            Section6ExcessDecay.correctorLegConst d) ≤ C * bb * s ^ (-3 : ℝ) := by
      calc
        _ ≤ Kr * ((CAb * Section6ExcessDecay.fractionalHolderConst d +
              Section6ExcessDecay.correctorLegConst d) * s ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hSourceCorrCoeff hKr0
        _ = (Kr * (CAb * Section6ExcessDecay.fractionalHolderConst d +
              Section6ExcessDecay.correctorLegConst d)) * s ^ (-3 : ℝ) := by ring
        _ ≤ (C * bb) * s ^ (-3 : ℝ) :=
          mul_le_mul_of_nonneg_right hAggCoeff hS3nonneg
        _ = C * bb * s ^ (-3 : ℝ) := by ring
    have hPowHolder0 : 0 ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * Hh :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hHh
    have hXHbound : Kr * XH ≤ XG := by
      have htmp : Kr *
            (CAb * Section6ExcessDecay.fractionalHolderConst d * s ^ (-3 : ℝ) *
                (3 : ℝ) ^ ((n : ℝ) / 2) * Hh +
              Section6ExcessDecay.correctorLegConst d *
                (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) ≤
          C * s ^ (-3 : ℝ) * bb * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
        calc
          _ = (Kr * (CAb * Section6ExcessDecay.fractionalHolderConst d *
                s ^ (-3 : ℝ) + Section6ExcessDecay.correctorLegConst d)) *
              ((3 : ℝ) ^ ((n : ℝ) / 2) * Hh) := by ring
          _ ≤ (C * bb * s ^ (-3 : ℝ)) *
                ((3 : ℝ) ^ ((n : ℝ) / 2) * Hh) :=
            mul_le_mul_of_nonneg_right hCoeffFinal hPowHolder0
          _ = _ := by ring
      simpa [XH, XHsrc, Corr, XG, bb, Hh, hbd] using htmp
    have hcombine := Section6ExcessDecay.excessDecayCombine
      (E := E) (Err := Err) (Sl := Sl) (Fg := Fg) (Tinv := Tinv) (J := J)
      (eps := epsilon) (XH := XH) (XG := XG) (Kc := Kc) (Kr := Kr)
      (CA := CAb) (CB := Cerr) (Cc := C) (bb := bb) (ss := ss) (s15 := s15)
      (pk := pk) (qn := qn) (r2 := Real.sqrt (d : ℝ) / 2)
      hE hErrn hSl hFg hTinv hJ heps0 hss hs15 hqn hKr0 hCAbpos.le
      honeB hDs hcap hKcle hb1 hb2 hb3 hXHbound
    simpa [E, Err, Sl, Fg, Tinv, J, bb, ss, s15, pk, qn, XG] using hcombine


end Paper
