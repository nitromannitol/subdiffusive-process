module

public import SubdiffusiveProcess.Paper.in_poincare
public import Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
public import Homogenization.Book.Ch03.Theorems.CoarsePoincare.NegativeBesov

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_poincare_negative_endpoint_pullback_memLp
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    MemLp (fun x : SpatialCoordinates d =>
      (v : SpatialCoordinates d → ℝ) (fun i => z i + r * x i))
      (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure
        (Homogenization.originCube d 0)) := by
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let S : Set (SpatialCoordinates d) := Homogenization.openCubeSet Q
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x i => z i + r * x i
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ d)⁻¹)
  have hpre : T ⁻¹' U = S := by
    ext x
    change T x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) ↔
      x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)
    rw [centeredCube_eq_pi z hr,
      Homogenization.mem_openCubeSet_originCube_iff]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    constructor
    · intro hx i
      rcases hx i with ⟨hlo, hhi⟩
      constructor <;> change _ < _ at * <;> nlinarith [hr]
    · intro hx i
      rcases hx i with ⟨hlo, hhi⟩
      constructor <;> change _ < _ <;> nlinarith [hr]
  have hsource : Homogenization.normalizedCubeMeasure Q = volume.restrict S := by
    rw [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure]
    have hvol : Homogenization.cubeVolume Q = 1 := by
      simp [Q, Homogenization.cubeVolume, Homogenization.cubeScaleFactor,
        Homogenization.originCube]
    rw [hvol]
    simp only [ENNReal.ofReal_one, inv_one, one_smul]
    exact Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hscale : Measure.map (fun x : SpatialCoordinates d => r • x) volume = c • volume := by
    simpa [c, Module.finrank_fintype_fun_eq_card,
      abs_of_pos (pow_pos hr d)] using
      (Measure.map_addHaar_smul (μ := (volume : Measure (SpatialCoordinates d))) hr.ne')
  have htrans : MeasurePreserving (fun y : SpatialCoordinates d => z + y) volume volume :=
    measurePreserving_add_left volume z
  have hmeasScale : Measurable (fun x : SpatialCoordinates d => r • x) := by fun_prop
  have hmeasTrans : Measurable (fun y : SpatialCoordinates d => z + y) := by fun_prop
  have hmeasT : Measurable T := by
    change Measurable (fun x : SpatialCoordinates d => z + r • x)
    fun_prop
  have hmapT : Measure.map T volume = c • volume := by
    have hcomp : T = (fun y : SpatialCoordinates d => z + y) ∘
        (fun x : SpatialCoordinates d => r • x) := by
      funext x
      ext i
      simp [T, Pi.smul_apply, smul_eq_mul]
    rw [hcomp, ← Measure.map_map hmeasTrans hmeasScale, hscale,
      Measure.map_smul c hmeasTrans.aemeasurable, htrans.map_eq]
  have hmapRestrict : (volume.restrict S).map T = c • volume.restrict U := by
    have h := Measure.restrict_map (μ := volume) hmeasT
      (centeredCube z r hr).isOpen.measurableSet
    rw [hmapT, hpre, Measure.restrict_smul] at h
    exact h.symm
  have hpres : MeasurePreserving T (volume.restrict S) (c • volume.restrict U) :=
    ⟨hmeasT, hmapRestrict⟩
  have htarget : MemLp (fun y : SpatialCoordinates d => (v : SpatialCoordinates d → ℝ) y)
      (2 : ℝ≥0∞) (c • volume.restrict U) := by
    apply (Lp.memLp v).smul_measure
    simp [c]
  have hcomp := htarget.comp_measurePreserving hpres
  rw [hsource]
  simpa [Function.comp_apply, T] using! hcomp

theorem inputs_poincare_negative_endpoint (d : ℕ) (hd : 2 ≤ d) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (u : SobolevData (centeredCube z r hr)) (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    BddAbove (Set.range (fun j : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
        (Homogenization.originCube d 0) s
        (fun x i => u.2 i (fun j => z j + r * x j)) j))) := by
  have _h_dim : 2 ≤ d := hd
  intro z r hr u s hs
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let F : Homogenization.Vec d → Homogenization.Vec d :=
    fun x i => u.2 i (fun j => z j + r * x j)
  have hF : MemLp F (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure Q) := by
    rw [MeasureTheory.memLp_pi_iff]
    intro i
    simpa only [F] using
      aux_inputs_poincare_negative_endpoint_pullback_memLp z r hr (u.2 i)
  let A : ℝ := Homogenization.cubeAverage Q (fun x => Homogenization.vecNormSq (F x))
  have hAnon : 0 ≤ A := by
    exact Homogenization.cubeAverage_nonneg_of_nonneg_on fun x hx =>
      Homogenization.vecNormSq_nonneg (F x)
  refine ⟨Real.sqrt A, ?_⟩
  rintro y ⟨j, rfl⟩
  change Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
    Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j) ≤
      Real.sqrt A
  have hdepth :
      Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j ≤ A := by
    rw [Homogenization.Book.Ch03.negativeBesovVectorDepthAverage_eq_old]
    exact Homogenization.cubeBesovNegativeVectorDepthAverage_le_cubeAverage_vecNormSq_of_memLp
      Q F j hF
  have hexp : -s * (j : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.1.le) (Nat.cast_nonneg j)
  have hweight : Real.rpow (3 : ℝ) (-s * (j : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j)
        ≤ 1 * Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j) :=
          mul_le_mul_of_nonneg_right hweight (Real.sqrt_nonneg _)
    _ = Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j) := by rw [one_mul]
    _ ≤ Real.sqrt A := Real.sqrt_le_sqrt hdepth

end Paper

