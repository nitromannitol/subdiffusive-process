module

public import SubdiffusiveProcess.Paper.lem_weighted_cluster_form_bounds
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper



lemma aux_lem_weighted_cluster_inverse_bounds_energy_bound
    {H I F G k : ℝ} (hk : 0 ≤ k) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hI : I ≤ F * G) (hHG : G ^ 2 ≤ H) (hHI : H ≤ k * I) :
    H ≤ k ^ 2 * F ^ 2 := by
  have hHFG : H ≤ k * (F * G) := by
    calc
      H ≤ k * I := hHI
      _ ≤ k * (F * G) := mul_le_mul_of_nonneg_left hI hk
  have hGG : G * G ≤ (k * F) * G := by
    have h := hHG.trans hHFG
    simpa [pow_two, mul_assoc] using h
  have hGle : G ≤ k * F := by
    rcases eq_or_ne G 0 with rfl | hG0
    · exact mul_nonneg hk hF
    · exact le_of_mul_le_mul_right hGG (lt_of_le_of_ne hG (Ne.symm hG0))
  calc
    H ≤ k * (F * G) := hHFG
    _ = (k * F) * G := by ring
    _ ≤ (k * F) * (k * F) :=
      mul_le_mul_of_nonneg_left hGle (mul_nonneg hk hF)
    _ = k ^ 2 * F ^ 2 := by ring

theorem lem_weighted_cluster_inverse_bounds
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (_hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a arho : ℕ → PositiveCoefficient (centeredCube z r hr))
    (lo hi : ℝ) (hlo : 0 < lo)
    (GrhoN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hGrhoN : ∀ n f, GrhoN n f =
      (responseSolution S (arho n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (H34sq : DomainL2 (centeredCube z r hr) → ℝ)
    (hH34def : ∀ u, H34sq u = ‖u‖ ^ 2 +
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (hfrac : ∀ (u : S.space),
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => u.val.1) < ⊤)
    (hcoercive : ∀ n (u : S.space),
      H34sq u.val.1 ≤ KN n * responseForm S (a n) u u)
    (hform : ∀ n (u : S.space),
      lo * responseForm S (a n) u u ≤ responseForm S (arho n) u u ∧
      responseForm S (arho n) u u ≤ hi * responseForm S (a n) u u) :
    ∀ n (f : DomainL2 (centeredCube z r hr)),
      H34sq (GrhoN n f) ≤ (KN n / lo) * inner ℝ f (GrhoN n f) ∧
      H34sq (GrhoN n f) ≤ (KN n / lo) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => GrhoN n f) < ⊤ := by
  intro n f
  let u : S.space := responseSolution S (arho n)
    ((sobolevVolumeLoad f).comp S.space.subtypeL)
  have hu : GrhoN n f = u.val.1 := by
    simpa [u] using hGrhoN n f
  have hresponse : responseForm S (arho n) u u =
      inner ℝ f (GrhoN n f) := by
    rw [responseSolution_spec]
    change inner ℝ f u.val.1 = inner ℝ f (GrhoN n f)
    rw [← hu]
  have hra : responseForm S (a n) u u ≤
      responseForm S (arho n) u u / lo := by
    apply (le_div_iff₀ hlo).2
    simpa [mul_comm] using (hform n u).1
  have hfirstU : H34sq u.val.1 ≤
      (KN n / lo) * inner ℝ f (GrhoN n f) := by
    calc
      H34sq u.val.1 ≤ KN n * responseForm S (a n) u u :=
        hcoercive n u
      _ ≤ KN n * (responseForm S (arho n) u u / lo) :=
        mul_le_mul_of_nonneg_left hra (hKN n)
      _ = (KN n / lo) * responseForm S (arho n) u u := by ring
      _ = (KN n / lo) * inner ℝ f (GrhoN n f) := by rw [hresponse]
  have hfirst : H34sq (GrhoN n f) ≤
      (KN n / lo) * inner ℝ f (GrhoN n f) := by
    simpa [hu] using hfirstU
  have hHlower : ‖GrhoN n f‖ ^ 2 ≤ H34sq (GrhoN n f) := by
    rw [hH34def]
    have hvol : 0 ≤ volume.real
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by positivity
    have hterm : 0 ≤ volume.real
        (centeredCube z r hr : Set (SpatialCoordinates d)) *
          (cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
            (fun _ : Fin 1 => GrhoN n f)).toReal ^ 2 :=
      mul_nonneg hvol (sq_nonneg _)
    linarith
  have hinner : inner ℝ f (GrhoN n f) ≤
      ‖f‖ * ‖GrhoN n f‖ := real_inner_le_norm _ _
  have hsecond : H34sq (GrhoN n f) ≤
      (KN n / lo) ^ 2 * ‖f‖ ^ 2 := by
    exact aux_lem_weighted_cluster_inverse_bounds_energy_bound
      (div_nonneg (hKN n) hlo.le) (norm_nonneg _) (norm_nonneg _)
      hinner hHlower hfirst
  have hthird : cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
      (fun _ : Fin 1 => GrhoN n f) < ⊤ := by
    simpa [hu] using hfrac u
  exact ⟨hfirst, hsecond, hthird⟩

end SubdiffusiveProcess.Paper
