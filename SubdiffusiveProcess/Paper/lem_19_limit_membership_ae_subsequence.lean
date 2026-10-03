module

public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Lane3.QueueHelpers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

/-- Fine proof step of Lemma 19 (paper 1943--1945).
Carried-input tick list:
- SOURCE: the parent lemma's actual L2 convergence `hlim` on the fixed cube;
  this is the paper's L2-convergent sequence and its L2 limit.
- CONCLUDED HERE: a strictly increasing subsequence whose scalar L2
  representatives converge almost everywhere on the cube to the scalar
  representative of the limit class.
The subsequence extraction is the paper's construction, not an added
hypothesis on the limit. -/
theorem lem_19_limit_membership_ae_subsequence
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (hthree : (threeQuarters : ℝ) = 3 / 4)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
    (vlim : DomainL2 (centeredCube z r hr))
    (hlim : Tendsto (fun n : ℕ => (w n).val 0) atTop (𝓝 vlim)) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∀ᵐ x ∂volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d)),
        Tendsto (fun j : ℕ => (w (sigma j)).val 0 x) atTop
          (𝓝 (vlim x)) := by
  have hconv :
      Tendsto
        (fun n : ℕ =>
          eLpNorm (fun x => (w n).val 0 x - vlim x) 2
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
        atTop (𝓝 0) := by
    simpa only [Pi.sub_apply] using!
      ((MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
        (fun n : ℕ => (w n).val 0) vlim).mp hlim)
  exact SubdiffusiveProcess.Lane3.exists_ae_subseq_of_eLpNorm_tendsto
    (SpatialCoordinates d)
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
    (fun n x => (w n).val 0 x) (vlim : SpatialCoordinates d → ℝ) 2
    (by norm_num) (fun n => (Lp.memLp ((w n).val 0)).aestronglyMeasurable) (Lp.memLp vlim).aestronglyMeasurable hconv

end Paper
