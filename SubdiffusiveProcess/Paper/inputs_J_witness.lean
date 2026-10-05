module

public import SubdiffusiveProcess.Paper.inputs_J_scalar_error_bounds
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.inputs_J_chart
public import SubdiffusiveProcess.Paper.inputs_J_chart_error_finite
public import SubdiffusiveProcess.Paper.inputs_J_deviation_by_J
public import SubdiffusiveProcess.Paper.inputs_J_matrices
public import SubdiffusiveProcess.Paper.inputs_J_ord_bounds
public import SubdiffusiveProcess.Paper.inputs_J_responseJ_isLUB
public import SubdiffusiveProcess.Paper.inputs_J_responseJ_scalar_hom
public import SubdiffusiveProcess.Paper.inputs_J_responseJ_split
public import SubdiffusiveProcess.Paper.inputs_J_responseJ_subadditive
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.LowerEllipticityComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsRecentring
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_inputs_J_witness_chart_dilation_descendant_ae
    (d : ℕ)
    (chart : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      PositiveCoefficient (centeredCube z r hr) → SpatialCoordinates d → ℝ →
        Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hchart : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
          ((chart z r hr a w r').coeffOn Q).toCoeffField x =
            Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i)))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (z' : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
    (b : PositiveCoefficient (centeredCube z' 1 h1))
    (hrel : ∀ᵐ y ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      b.val y = a.val (fun i => z i + r * (y i - z' i))) :
    ∀ (k : ℤ) (R : Homogenization.TriadicCube d),
      R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) k →
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((chart z r hr a z r).coeffOn R)
        ((chart z' 1 h1 b z' 1).coeffOn R) := by
  have hset : (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z'
        (Homogenization.openCubeSet (Homogenization.originCube d 0)) := by
    calc
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) =
          Homogenization.translateSet z'
            (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
              Set (SpatialCoordinates d)) := by
        ext x
        rw [centeredCube_eq_pi z' h1, Homogenization.mem_translateSet_iff_sub_mem,
          centeredCube_eq_pi (0 : SpatialCoordinates d) (by norm_num)]
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
        constructor
        · intro hx i
          constructor <;> dsimp at * <;> linarith [hx i]
        · intro hx i
          constructor <;> dsimp at * <;> linarith [hx i]
      _ = Homogenization.translateSet z'
          (Homogenization.openCubeSet (Homogenization.originCube d 0)) := by
        rw [← _root_.SubdiffusiveProcess.EllipticRegularity.centeredCube_zero_eq_openCubeSet_originCube
          (d := d) 0 (by norm_num)]
        congr 1
  have hrel' : b.val =ᵐ[volume.restrict
      (Homogenization.translateSet z'
        (Homogenization.openCubeSet (Homogenization.originCube d 0)))]
      (fun y => a.val (fun i => z i + r * (y i - z' i))) := by
    exact hrel.filter_mono (by rw [← hset])
  have hmp := Homogenization.measurePreserving_addRight_restrict_translateSet
    (d := d) z' (Homogenization.openCubeSet (Homogenization.originCube d 0))
  have hshift := hmp.quasiMeasurePreserving.ae_eq_comp hrel'
  have hroot : (fun x : SpatialCoordinates d => b.val (x + z')) =ᵐ[
      volume.restrict (Homogenization.openCubeSet
        (Homogenization.originCube d 0))]
      (fun x => a.val (fun i => z i + r * x i)) := by
    filter_upwards [hshift] with x hx
    simpa [Function.comp_apply, Pi.add_apply, add_sub_cancel_right] using hx
  intro k R hR
  have hk : k ≤ (Homogenization.originCube d 0).scale :=
    Homogenization.descendant_scale_le_of_mem_descendantsAtScale hR
  have hsub := Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
    hk hR
  have hrootR := hroot.filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set volume hsub))
  have hA := hchart z r hr a z r hr (Set.Subset.rfl :
      (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d))) R hsub
  have hB := hchart z' 1 h1 b z' 1 h1 (Set.Subset.rfl :
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) ⊆
        (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) R hsub
  change ((chart z r hr a z r).coeffOn R).toCoeffField =ᵐ[
    volume.restrict (Homogenization.openCubeSet R)]
      ((chart z' 1 h1 b z' 1).coeffOn R).toCoeffField
  filter_upwards [hA, hB, hrootR] with x hxA hxB hxrel
  calc
    ((chart z r hr a z r).coeffOn R).toCoeffField x =
        Homogenization.scalarMatrix (a.val (fun i => z i + r * x i)) := hxA
    _ = Homogenization.scalarMatrix (b.val (fun i => z' i + 1 * x i)) := by
      congr 1
      simp only [one_mul]
      rw [show (fun i => z' i + x i) = x + z' from by
        funext i; exact add_comm _ _]
      exact hxrel.symm
    _ = ((chart z' 1 h1 b z' 1).coeffOn R).toCoeffField x := hxB.symm

lemma aux_inputs_J_witness_sigmaStarInv_uniform_bound
    (d : ℕ) [NeZero d] (A : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (n : ℕ) :
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ)) A ≤
      max 1 (4 * (d : ℝ) * (A.coeffOn (Homogenization.originCube d 0)).lam⁻¹) := by
  let Q := Homogenization.originCube d 0
  let F : Homogenization.CoeffField d :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
      (Homogenization.Book.Ch02.cubeDomain Q) (A.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hEll : Homogenization.IsEllipticFieldOn
      (A.coeffOn Q).lam (A.coeffOn Q).Lam
      (Homogenization.openCubeSet Q) F := by
    simpa [F] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Homogenization.Book.Ch02.cubeDomain Q) (A.coeffOn Q)
  have hData : Homogenization.OpenCubeDescendantDeterministicCoarseData Q F := by
    simpa [F] using
      Homogenization.Book.Ch02.pointwiseCoeffField_openCube_descendant_data
        Q (A.coeffOn Q)
  have hmatrix :
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) A ≤
        Homogenization.maxDescendantSigmaStarInvNormAtScale Q
          (Q.scale - (n : ℤ)) F := by
    exact Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
      A Q hk
  have hblock :
      Homogenization.maxDescendantSigmaStarInvNormAtScale Q
          (Q.scale - (n : ℤ)) F ≤
        4 * (Fintype.card (Fin d) : ℝ) * (A.coeffOn Q).lam⁻¹ := by
    simpa [F] using
      Homogenization.maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := F) hEll hData n
  calc
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) A ≤
        Homogenization.maxDescendantSigmaStarInvNormAtScale Q
          (Q.scale - (n : ℤ)) F := hmatrix
    _ ≤ 4 * (d : ℝ) * (A.coeffOn Q).lam⁻¹ := by simpa using hblock
    _ ≤ max 1 (4 * (d : ℝ) * (A.coeffOn Q).lam⁻¹) := le_max_right _ _

lemma aux_inputs_J_witness_lambda_lower_floor
    (d : ℕ) [NeZero d] (A : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) (q : Homogenization.Book.Ch02.MultiscaleExponent)
    (hq : q.IsAdmissible) :
    (max 1 (4 * (d : ℝ) *
      (A.coeffOn (Homogenization.originCube d 0)).lam⁻¹))⁻¹ ≤
      Homogenization.Book.Ch02.lambdaSq
        (Homogenization.originCube d 0) s q A := by
  classical
  let Q := Homogenization.originCube d 0
  let C : ℝ := max 1 (4 * (d : ℝ) * (A.coeffOn Q).lam⁻¹)
  have hC : 1 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  cases q with
  | finite p =>
      have hpone : 1 ≤ p := by simpa using hq
      have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hpone
      let H : ℕ → ℝ := fun n =>
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          Q (Q.scale - (n : ℤ)) A
      let S : ℝ := ∑' n : ℕ,
        Homogenization.geometricWeight s p n * Real.rpow (H n) (p / 2)
      have hSsum : Summable (fun n : ℕ =>
          Homogenization.geometricWeight s p n * Real.rpow (H n) (p / 2)) := by
        simpa [H, Homogenization.Book.Ch02.geometricWeight_eq_old] using
          Homogenization.Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField
            Q A hs hppos
      have hweights : Summable (fun n : ℕ => Homogenization.geometricWeight s p n) :=
        Homogenization.summable_geometricWeight (mul_pos hs hppos)
      have hweightsum : (∑' n : ℕ, Homogenization.geometricWeight s p n) = 1 :=
        Homogenization.tsum_geometricWeight_eq_one (mul_pos hs hppos)
      have hterms : ∀ n : ℕ,
          Homogenization.geometricWeight s p n * Real.rpow (H n) (p / 2) ≤
            Homogenization.geometricWeight s p n * Real.rpow C (p / 2) := by
        intro n
        have hn : Q.scale - (n : ℤ) ≤ Q.scale :=
          sub_le_self _ (by exact_mod_cast Nat.zero_le n)
        have hHnonneg : 0 ≤ H n := by
          exact Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg
            Q hn A
        have hHle : H n ≤ C := by
          dsimp [H, Q, C]
          exact aux_inputs_J_witness_sigmaStarInv_uniform_bound d A n
        have hpow : Real.rpow (H n) (p / 2) ≤ Real.rpow C (p / 2) :=
          Real.rpow_le_rpow hHnonneg hHle (by positivity)
        have hw : 0 ≤ Homogenization.geometricWeight s p n :=
          Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hppos.le)
        exact mul_le_mul_of_nonneg_left hpow hw
      have hconstsum : Summable (fun n : ℕ =>
          Homogenization.geometricWeight s p n * Real.rpow C (p / 2)) :=
        hweights.mul_right (Real.rpow C (p / 2))
      have hSbound : S ≤ Real.rpow C (p / 2) := by
        calc
          S ≤ ∑' n : ℕ,
              Homogenization.geometricWeight s p n * Real.rpow C (p / 2) :=
            Summable.tsum_le_tsum hterms hSsum hconstsum
          _ = Real.rpow C (p / 2) := by
            rw [tsum_mul_right, hweightsum]
            ring
      have hlambda : 0 < Homogenization.Book.Ch02.lambdaSq Q s (.finite p) A :=
        Homogenization.Book.Ch02.lambdaSq_pos Q A hs (by simpa using hpone)
      have hSpos : 0 < S := by
        have hrepr := Homogenization.Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
          Q s p A hppos (mul_nonneg hs.le hppos.le)
        have hrepr' : Real.rpow
            (Homogenization.Book.Ch02.lambdaSq Q s (.finite p) A) (-p / 2) = S := by
          simpa [S, Homogenization.Book.Ch02.geometricWeight_eq_old] using hrepr
        rw [← hrepr']
        exact Real.rpow_pos_of_pos hlambda _
      have hCpowpos : 0 < Real.rpow C (p / 2) :=
        Real.rpow_pos_of_pos hCpos _
      have hinv : (Real.rpow C (p / 2))⁻¹ ≤ S⁻¹ :=
        (inv_le_inv₀ hCpowpos hSpos).2 hSbound
      have hexp : 0 < 2 / p := by positivity
      have hpow :
          Real.rpow ((Real.rpow C (p / 2))⁻¹) (2 / p) ≤
            Real.rpow (S⁻¹) (2 / p) :=
        Real.rpow_le_rpow (inv_nonneg.mpr hCpowpos.le) hinv hexp.le
      have hleft : Real.rpow ((Real.rpow C (p / 2))⁻¹) (2 / p) = C⁻¹ := by
        calc
          Real.rpow ((Real.rpow C (p / 2))⁻¹) (2 / p) =
              Real.rpow (Real.rpow C (p / 2)) (-(2 / p)) :=
            (Real.rpow_neg_eq_inv_rpow (Real.rpow C (p / 2)) (2 / p)).symm
          _ = Real.rpow C ((p / 2) * (-(2 / p))) := by
            exact (Real.rpow_mul hCpos.le (p / 2) (-(2 / p))).symm
          _ = C⁻¹ := by
            rw [show (p / 2) * (-(2 / p)) = -1 by field_simp]
            simpa using (Real.rpow_neg hCpos.le (1 : ℝ))
      have hright : Real.rpow (S⁻¹) (2 / p) =
          Homogenization.Book.Ch02.lambdaSq Q s (.finite p) A := by
        calc
          Real.rpow (S⁻¹) (2 / p) = Real.rpow S (-(2 / p)) :=
            (Real.rpow_neg_eq_inv_rpow S (2 / p)).symm
          _ = Homogenization.Book.Ch02.lambdaSq Q s (.finite p) A := by
            simp [Homogenization.Book.Ch02.lambdaSq,
              Homogenization.Book.Ch02.lambdaSqFinite,
              Homogenization.Book.Ch02.geometricWeight_eq_old, S, H]
      calc
        C⁻¹ = Real.rpow ((Real.rpow C (p / 2))⁻¹) (2 / p) := hleft.symm
        _ ≤ Real.rpow (S⁻¹) (2 / p) := hpow
        _ = Homogenization.Book.Ch02.lambdaSq Q s (.finite p) A := hright
  | infinity =>
      let Dset : Set ℝ := {x | ∃ n : ℕ,
        x = Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
          Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            Q (Q.scale - (n : ℤ)) A}
      have hDpos : 0 < sSup Dset := by
        simpa [Dset, Q] using
          Homogenization.Book.Ch02.lambdaSqInfinity_denominator_pos Q A hs
      have hmem : Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q A ∈ Dset := by
        refine ⟨0, ?_⟩
        simp [Q,
          Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_self]
      have hDle : sSup Dset ≤ C := by
        apply csSup_le ⟨_, hmem⟩
        intro x hx
        rcases hx with ⟨n, rfl⟩
        have hn : Q.scale - (n : ℤ) ≤ Q.scale :=
          sub_le_self _ (by exact_mod_cast Nat.zero_le n)
        have hweight : Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) ≤ 1 :=
          Homogenization.Book.Ch02.infinityWeight_le_one hs.le n
        have hHnonneg : 0 ≤
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              Q (Q.scale - (n : ℤ)) A :=
          Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg
            Q hn A
        have hHle :
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              Q (Q.scale - (n : ℤ)) A ≤ C := by
          dsimp [C, Q]
          exact aux_inputs_J_witness_sigmaStarInv_uniform_bound d A n
        calc
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
                Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                  Q (Q.scale - (n : ℤ)) A ≤ 1 * C :=
            mul_le_mul hweight hHle hHnonneg zero_le_one
          _ = C := by ring
      have hInv : C⁻¹ ≤ (sSup Dset)⁻¹ :=
        (inv_le_inv₀ hCpos hDpos).2 hDle
      simpa [Homogenization.Book.Ch02.lambdaSq,
        Homogenization.Book.Ch02.lambdaSqInfinity, Dset, Q, C] using hInv

lemma aux_inputs_J_witness_exponent_admissible (q : ℝ≥0∞)
    (hq : q = ⊤ ∨ 1 ≤ q) :
    (if q = ⊤ then Homogenization.Book.Ch02.MultiscaleExponent.infinity
      else Homogenization.Book.Ch02.MultiscaleExponent.finite q.toReal).IsAdmissible := by
  rcases hq with htop | hq
  · simp [htop]
  · by_cases htop : q = ⊤
    · simp [htop]
    · have hqReal : 1 ≤ q.toReal :=
        (ENNReal.toReal_le_toReal (by norm_num) htop).mpr hq
      simpa [htop] using hqReal

lemma aux_inputs_J_witness_chart_symmetric (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ)
    (Q : Homogenization.TriadicCube d) :
    (aux_inputs_J_chart_construct z r hr a w r').coeffOn Q |>.IsSymmetric := by
  filter_upwards with x
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [aux_inputs_J_chart_construct, aux_inputs_J_chart_clippedData,
    SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData.toTriadicCoeffFamily,
    SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
    SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [hij, Ne.symm hij]

theorem inputs_J_witness (d : ℕ) (hd : 2 ≤ d) :
    (Nonempty (_root_.SubdiffusiveProcess.Paper.in_J d)) := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  let chart := fun (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr)) (w : SpatialCoordinates d)
      (r' : ℝ) => aux_inputs_J_chart_construct z r hr a w r'
  have hchart : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr)) (w : SpatialCoordinates d)
      (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
          ((chart z r hr a w r').coeffOn Q).toCoeffField x =
            Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i)) := by
    intro z r hr a w r' hr' hinner Q hQ
    exact aux_inputs_J_chart_construct_eq z r hr a w r' hr' hinner Q hQ
  let exponent := fun q : ℝ≥0∞ =>
    if q = ⊤ then Homogenization.Book.Ch02.MultiscaleExponent.infinity
    else Homogenization.Book.Ch02.MultiscaleExponent.finite q.toReal
  let lowerEnvelope := fun (A : Homogenization.Book.Ch02.TriadicCoeffFamily d)
      (e : Homogenization.Book.Ch02.MultiscaleExponent) =>
    sInf {x : ℝ | ∃ t : ℝ, 0 < t ∧
      x = Homogenization.Book.Ch02.lambdaSq
        (Homogenization.originCube d 0) t e A}
  let lam := fun (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr)) (w : SpatialCoordinates d)
      (r' s : ℝ) (q : ℝ≥0∞) =>
    if q = ⊤ ∨ 1 ≤ q then
      if 0 < s then
        Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) s
          (exponent q) (chart z r hr a w r')
      else lowerEnvelope (chart z r hr a w r') (exponent q)
    else
      (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
        (Homogenization.originCube d 0) (chart z r hr a w r'))⁻¹
  let Lam := fun (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr)) (w : SpatialCoordinates d)
      (r' s : ℝ) (q : ℝ≥0∞) =>
    if 0 < s ∧ (q = ⊤ ∨ 1 ≤ q) then
      Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) s
        (exponent q) (chart z r hr a w r')
    else Homogenization.Book.Ch02.coarseBMatrixNorm
      (Homogenization.originCube d 0) (chart z r hr a w r')
  let err := fun (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr)) (w : SpatialCoordinates d)
      (r' a₀ s : ℝ) (q : ℝ≥0∞) =>
    (if q = ⊤ then
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
          (Homogenization.originCube d 0) 0 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (chart z r hr a w r') a₀
      else
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
          (Homogenization.originCube d 0) 0 s
          Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal
          (chart z r hr a w r') a₀).toReal
  refine ⟨{
    lam := lam
    Lam := Lam
    err := err
    chart := chart
    chart_eq := hchart
    lam_eq := ?_
    Lam_eq := ?_
    err_finite := ?_
    err_eq := ?_
    lam_pos := ?_
    Lam_pos := ?_
    err_nonneg := ?_
    lam_mono := ?_
    responseJ_isLUB := _root_.SubdiffusiveProcess.Paper.inputs_J_responseJ_isLUB d hd
    matrices := _root_.SubdiffusiveProcess.Paper.inputs_J_matrices d hd
    responseJ_split := _root_.SubdiffusiveProcess.Paper.inputs_J_responseJ_split d hd
    ord_bounds := _root_.SubdiffusiveProcess.Paper.inputs_J_ord_bounds d hd
    responseJ_subadditive := _root_.SubdiffusiveProcess.Paper.inputs_J_responseJ_subadditive d hd
    responseJ_scalar_hom := _root_.SubdiffusiveProcess.Paper.inputs_J_responseJ_scalar_hom d hd
    deviation_by_J := _root_.SubdiffusiveProcess.Paper.inputs_J_deviation_by_J d hd
    lam_dilation := ?_
    Lam_dilation := ?_
    bound_ellipticities_by_error := ?_ }⟩
  · intro z r hr a w r' hr' hsub s hs q hq
    simp [lam, hs.1, hq, exponent]
  · intro z r hr a w r' hr' hsub s hs q hq
    simp [Lam, hs.1, hq, exponent]
  · exact _root_.SubdiffusiveProcess.Paper.inputs_J_chart_error_finite d hd chart hchart
  · intro z r hr a w r' hr' hsub s hs q hq a₀ ha₀
    rfl
  · intro z r hr a w r' s q
    simp only [lam]
    by_cases hqvalid : q = ⊤ ∨ 1 ≤ q
    · simp only [ite_eq_left hqvalid]
      by_cases hspos : 0 < s
      · simp only [ite_eq_left hspos]
        exact Homogenization.Book.Ch02.lambdaSq_pos
          (Homogenization.originCube d 0) (chart z r hr a w r') hspos
          (aux_inputs_J_witness_exponent_admissible q hqvalid)
      · simp only [ite_eq_right hspos]
        let C : ℝ := max 1 (4 * (d : ℝ) *
          ((chart z r hr a w r').coeffOn (Homogenization.originCube d 0)).lam⁻¹)
        have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (by
          dsimp [C]
          exact le_max_left _ _)
        have hne : {x : ℝ | ∃ t : ℝ, 0 < t ∧
            x = Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0)
              t (exponent q) (chart z r hr a w r')}.Nonempty := by
          exact ⟨Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0)
            1 (exponent q) (chart z r hr a w r'), 1, by norm_num, rfl⟩
        have hfloor : C⁻¹ ≤ sInf {x : ℝ | ∃ t : ℝ, 0 < t ∧
            x = Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0)
              t (exponent q) (chart z r hr a w r')} := by
          apply le_csInf hne
          intro x hx
          rcases hx with ⟨t, ht, rfl⟩
          dsimp [C]
          exact aux_inputs_J_witness_lambda_lower_floor d (chart z r hr a w r')
            ht (exponent q) (aux_inputs_J_witness_exponent_admissible q hqvalid)
        have hCinv : 0 < C⁻¹ := inv_pos.mpr hCpos
        simpa [lowerEnvelope] using lt_of_lt_of_le hCinv hfloor
    · simp only [ite_eq_right hqvalid]
      exact inv_pos.mpr
        (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_pos
          (Homogenization.originCube d 0) (chart z r hr a w r'))
  · intro z r hr a w r' s q
    simp only [Lam]
    by_cases hvalid : 0 < s ∧ (q = ⊤ ∨ 1 ≤ q)
    · simp only [ite_eq_left hvalid]
      rcases hvalid with ⟨hs, hqvalid⟩
      exact Homogenization.Book.Ch02.LambdaSq_pos
        (Homogenization.originCube d 0) (chart z r hr a w r') hs
        (aux_inputs_J_witness_exponent_admissible q hqvalid)
    · simp only [ite_eq_right hvalid]
      exact Homogenization.Book.Ch02.coarseBMatrixNorm_pos
        (Homogenization.originCube d 0) (chart z r hr a w r')
  · intro z r hr a w r' a₀ s q
    simp only [err]
    exact ENNReal.toReal_nonneg
  · intro z r hr a w r' q s s' hss
    simp only [lam]
    by_cases hqvalid : q = ⊤ ∨ 1 ≤ q
    · simp only [ite_eq_left hqvalid]
      have hadm := aux_inputs_J_witness_exponent_admissible q hqvalid
      by_cases hspos : 0 < s
      · have hs'pos : 0 < s' := lt_of_lt_of_le hspos hss
        simp only [ite_eq_left hspos, ite_eq_left hs'pos]
        by_cases heq : s = s'
        · subst s'
          exact le_rfl
        · exact Homogenization.Book.Ch02.lambdaSq_mono
            (Homogenization.originCube d 0) (chart z r hr a w r') hspos
            (lt_of_le_of_ne hss heq) hadm
      · by_cases hs'pos : 0 < s'
        · simp only [ite_eq_right hspos, ite_eq_left hs'pos]
          have hbdd : BddBelow {x : ℝ | ∃ t : ℝ, 0 < t ∧
              x = Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0)
                t (exponent q) (chart z r hr a w r')} := by
            refine ⟨(max 1 (4 * (d : ℝ) *
              ((chart z r hr a w r').coeffOn (Homogenization.originCube d 0)).lam⁻¹))⁻¹,
              ?_⟩
            intro x hx
            rcases hx with ⟨t, ht, rfl⟩
            exact aux_inputs_J_witness_lambda_lower_floor d (chart z r hr a w r')
              ht (exponent q) hadm
          exact csInf_le hbdd ⟨s', hs'pos, rfl⟩
        · simp only [ite_eq_right hspos, ite_eq_right hs'pos]
          exact le_rfl
    · simp only [ite_eq_right hqvalid]
      exact le_rfl
  · intro z r hr a z' h1 b hrel s q
    simp only [lam]
    have hdesc := aux_inputs_J_witness_chart_dilation_descendant_ae d chart hchart
      z r hr a z' h1 b hrel
    let Q := Homogenization.originCube d 0
    have hroot : Homogenization.Book.Ch02.CoeffOn.AEEq
        ((chart z r hr a z r).coeffOn Q)
        ((chart z' 1 h1 b z' 1).coeffOn Q) := by
      apply hdesc 0 Q
      have hscale : Q.scale = 0 := rfl
      have hself : Q ∈ Homogenization.descendantsAtScale Q Q.scale := by
        rw [Homogenization.descendantsAtScale_self]
        simp
      simpa [hscale, Q] using hself
    by_cases hqvalid : q = ⊤ ∨ 1 ≤ q
    · simp only [ite_eq_left hqvalid]
      have hLambdaEq : ∀ t : ℝ,
          Homogenization.Book.Ch02.lambdaSq Q t (exponent q)
              (chart z r hr a z r) =
            Homogenization.Book.Ch02.lambdaSq Q t (exponent q)
              (chart z' 1 h1 b z' 1) := fun t =>
        SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.lambdaSq_eq_of_descendantAEEq
          Q hdesc t (exponent q)
      by_cases hspos : 0 < s
      · simp only [ite_eq_left hspos]
        exact hLambdaEq s
      · simp only [ite_eq_right hspos]
        have hset :
            {x : ℝ | ∃ t : ℝ, 0 < t ∧
              x = Homogenization.Book.Ch02.lambdaSq Q t (exponent q)
                (chart z r hr a z r)} =
            {x : ℝ | ∃ t : ℝ, 0 < t ∧
              x = Homogenization.Book.Ch02.lambdaSq Q t (exponent q)
                (chart z' 1 h1 b z' 1)} := by
          ext x
          constructor
          · rintro ⟨t, ht, rfl⟩
            exact ⟨t, ht, hLambdaEq t⟩
          · rintro ⟨t, ht, rfl⟩
            exact ⟨t, ht, (hLambdaEq t).symm⟩
        change sInf {x : ℝ | ∃ t : ℝ, 0 < t ∧
          x = Homogenization.Book.Ch02.lambdaSq Q t (exponent q)
            (chart z r hr a z r)} =
          sInf {x : ℝ | ∃ t : ℝ, 0 < t ∧
          x = Homogenization.Book.Ch02.lambdaSq Q t (exponent q)
            (chart z' 1 h1 b z' 1)}
        exact congrArg sInf hset
    · simp only [ite_eq_right hqvalid]
      change (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (chart z r hr a z r))⁻¹ =
        (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
          (chart z' 1 h1 b z' 1))⁻¹
      exact congrArg (fun x : ℝ => x⁻¹)
        (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.coarseSigmaStarInvMatrixNorm_eq_of_localAEEq
          hroot)
  · intro z r hr a z' h1 b hrel s q
    simp only [Lam]
    by_cases hvalid : 0 < s ∧ (q = ⊤ ∨ 1 ≤ q)
    · simp only [ite_eq_left hvalid]
      exact (SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.LambdaSq_eq_of_descendantAEEq
        (Homogenization.originCube d 0)
        (aux_inputs_J_witness_chart_dilation_descendant_ae d chart hchart
          z r hr a z' h1 b hrel) s (exponent q))
    · simp only [ite_eq_right hvalid]
      let Q := Homogenization.originCube d 0
      have hdesc := aux_inputs_J_witness_chart_dilation_descendant_ae d chart hchart
        z r hr a z' h1 b hrel
      have hroot : Homogenization.Book.Ch02.CoeffOn.AEEq
          ((chart z r hr a z r).coeffOn Q)
          ((chart z' 1 h1 b z' 1).coeffOn Q) := by
        apply hdesc 0 Q
        have hscale : Q.scale = 0 := rfl
        have hself : Q ∈ Homogenization.descendantsAtScale Q Q.scale := by
          rw [Homogenization.descendantsAtScale_self]
          simp
        simpa [hscale, Q] using hself
      exact SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.coarseBMatrixNorm_eq_of_localAEEq
        hroot
  · intro z r hr a w r' a0 ha0 s hs q hq
    have hSymm : ∀ Q : Homogenization.TriadicCube d,
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric ((chart z r hr a w r').coeffOn Q) :=
      aux_inputs_J_witness_chart_symmetric d z r hr a w r'
    rcases hq with rfl | rfl
    · have H := inputs_J_scalar_error_bounds d (Homogenization.originCube d 0)
        (chart z r hr a w r') hSymm a0 ha0 s hs 1 (Or.inl rfl)
      simpa [lam, Lam, err, exponent, hs.1,
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError, Homogenization.originCube] using H.2
    · have H := inputs_J_scalar_error_bounds d (Homogenization.originCube d 0)
        (chart z r hr a w r') hSymm a0 ha0 s hs 2 (Or.inr rfl)
      simpa [lam, Lam, err, exponent, hs.1,
        SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError, Homogenization.originCube] using H.2

end SubdiffusiveProcess.Paper

