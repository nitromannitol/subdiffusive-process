import SubdiffusiveProcess.Paper.prop_killed_inverse_collective_compactness
import SubdiffusiveProcess.Paper.prop_killed_inverse_injectivity
import SubdiffusiveProcess.Paper.prop_killed_inverse_spectral_square_root
import SubdiffusiveProcess.Paper.prop_killed_inverse_dirichlet_form
import SubdiffusiveProcess.Paper.prop_killed_inverse_form_density
import SubdiffusiveProcess.Paper.killed_inverse_mosco
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.Lane2.MeshGluing
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_prop_killed_inverse_moscoS
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (EN : ℕ → DomainL2 Ω → EReal)
    (hEN : ∀ (n : ℕ) (u : DomainL2 Ω),
      EN n u = sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
        e = (responseForm S (a n) w w : EReal)})
    (hMoscoLower : ∀ (uN : ℕ → DomainL2 Ω) (u : DomainL2 Ω),
      (∀ f : DomainL2 Ω,
        Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G u ≤ liminf (fun n => EN n (uN n)) atTop)
    (uN : ℕ → S.space) (u : DomainL2 Ω)
    (hweak : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) :
    limitFormEnergy G u ≤
      liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop := by
  apply le_trans (hMoscoLower (fun n => (uN n).val.1) u hweak)
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => by
    rw [hEN n]
    exact sInf_le ⟨uN n, rfl, rfl⟩)

/-- proposition `mfd:prop-killed-inverse` (paper lines 1775-1877), ALL clauses, with the
concrete standing inputs pinned; DEV-030-G4-killed-inverse-standing-inputs.

The space `S` is pinned to the killed Sobolev graph (`hS`), the family `GN` is the actual
finite inverse responses (`hGN`), the coercivity constants come as a single common `K`
(`hCoercive`, source `lem_coercivity` + `conv_represented_sequence`), the interpolation
input is the published fractional compact-embedding input (Rellich on cubes, encoded in
`CubeFractionalInterpolationInput`) (`hInterp`), the dense test catalog is the
countable rational submodule `D` with smooth compactly supported representatives
(`D`/`hDcount`/`hDdense`/`hDsmooth`), the quadratic responses are actual inverse responses
(`hresponse`, `conv_represented_sequence` / `prop_response_compact`), and the mesh
interpolant is CARRIED from the independent finite `mesh_interpolator` statement together
with `lem_extension` (`hmesh`). No compactness of the responses and no strong-response
limit are assumed here. The killed energies on the ambient `DomainL2` carrier are represented
by `EN` with their exact extension-by-`+∞`/infimum interface `hEN`, supplied by
`killed_inverse_mosco`; this is what makes the weak lower-bound sequence arbitrary in `L²`.

Doc tick suppliers:
- hcontract: deferred Stampacchia Sobolev normal-contraction chain rule,
  accepted external input, paper 1869–1871; finite-cutoff stability only.
- `lem_coercivity` + `conv_represented_sequence` for `K` and coercivity;
- `CubeFractionalInterpolationInput` for `hInterp` (published fractional compact-embedding input, Rellich on cubes);
- `conv_represented_sequence` and `prop_response_compact` for `D` and `hresponse`;
- `mesh_interpolator` + `lem_extension` for `hmesh`;
- `in_killed_inverse` for `hGN`;
- `killed_inverse_mosco` for `EN` and `hEN`.

The conclusion retains, in the same order, the unique operator-norm limit `G`, compact,
self-adjoint, positive and injective; the identification of `D(E)` with the range of the
positive self-adjoint square root of `G`; that the dual energy of `G` is a densely defined
closed `DirichletForm`; both Mosco clauses (weak `L²` lower bound for arbitrary `u` and
recovery in `S.space`); and the form-norm density of the functions `G f` for smooth
compactly supported `f`. -/
theorem prop_killed_inverse
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hcontract : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧
        responseForm S (a n) v v ≤ responseForm S (a n) u u)
    (GN : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z R hR)), GN n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ (n : ℕ) (v : S.space),
      cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        K * responseForm S (a n) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (hDcount : (D : Set (DomainL2 (centeredCube z R hR))).Countable)
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z R hR))))
    (hDsmooth : ∀ f : D,
      ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc)
    (hresponse : ∀ f : D, CauchySeq (fun n => inner ℝ f.val (GN n f.val)))
    (EN : ℕ → DomainL2 (centeredCube z R hR) → EReal)
    (hEN : ∀ (n : ℕ) (u : DomainL2 (centeredCube z R hR)),
      EN n u = sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
        e = (responseForm S (a n) w w : EReal)})
    (hmesh : ∀ φ : DomainL2 (centeredCube z R hR),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (a n) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε)) :
    ∃! G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR),
      -- the operator-norm limit and its four properties
      (Tendsto GN atTop (𝓝 G) ∧ IsCompactOperator G ∧
        (∀ x y : DomainL2 (centeredCube z R hR),
          inner ℝ (G x) y = inner ℝ x (G y)) ∧
        (∀ x : DomainL2 (centeredCube z R hR), 0 ≤ inner ℝ x (G x)) ∧
        Function.Injective G) ∧
      -- `D(E) = Ran G^{1/2}`, through the positive self-adjoint square root
      (∃ Rroot : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR),
        (∀ x y : DomainL2 (centeredCube z R hR),
          inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
        (∀ x : DomainL2 (centeredCube z R hR), 0 ≤ inner ℝ x (Rroot x)) ∧
        Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot) ∧
      -- the dual energy of `G` is a densely defined closed `DirichletForm`
      (∃ EForm : _root_.DirichletForm
          (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))),
        (∀ w : DomainL2 (centeredCube z R hR),
          EForm.toClosedForm.energy w = limitFormEnergy G w) ∧
        DirichletForm.HasNormalContractions EForm) ∧
      -- Mosco: the weak lower bound and the recovery sequences
      ((∀ (uN : ℕ → DomainL2 (centeredCube z R hR)) (u : DomainL2 (centeredCube z R hR)),
          (∀ f : DomainL2 (centeredCube z R hR),
            Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) →
          limitFormEnergy G u ≤
            liminf (fun n => EN n (uN n)) atTop) ∧
        (∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
          Tendsto (fun n => ((w n).val.1,
            ((responseForm S (a n) (w n) (w n) : ℝ) : EReal))) atTop
            (𝓝 (u, limitFormEnergy G u)))) ∧
      -- the functions `G f`, `f` smooth and compactly supported, are form-dense
      (∀ u ∈ limitFormDomain G, ∀ ε : ℝ, 0 < ε →
        ∃ f : DomainL2 (centeredCube z R hR),
          (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
            tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
            (f : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc) ∧
          ‖u - G f‖ ≤ ε ∧ limitFormEnergy G (u - G f) ≤ ((ε : ℝ) : EReal)) := by
  obtain ⟨G, hGprop, huniq⟩ :=
    killed_inverse_mosco d hd z R hR S hS a GN hGN hInterp K hK hCoercive D hDcount hDdense
      hDsmooth hresponse EN hEN
  obtain ⟨⟨hTend, hComp, hSymm, hPos⟩, hMoscoLower, hMoscoRecov⟩ := hGprop
  have hInj : Function.Injective G :=
    prop_killed_inverse_injectivity d hd z R hR S a GN G hGN hTend D hDdense hDsmooth hmesh
  obtain ⟨Rroot, hRsymm, hRpos, hRcomp, hRdom⟩ :=
    prop_killed_inverse_spectral_square_root (Q := centeredCube z R hR) G hComp hSymm hPos hInj
  have hroot : ∃ Rroot' : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR),
      (∀ x y : DomainL2 (centeredCube z R hR), inner ℝ (Rroot' x) y = inner ℝ x (Rroot' y)) ∧
      (∀ x : DomainL2 (centeredCube z R hR), 0 ≤ inner ℝ x (Rroot' x)) ∧
      Rroot'.comp Rroot' = G ∧ limitFormDomain G = Set.range Rroot' :=
    ⟨Rroot, hRsymm, hRpos, hRcomp, hRdom⟩
  have hMoscoS : ∀ (uN : ℕ → S.space) (u : DomainL2 (centeredCube z R hR)),
      (∀ f : DomainL2 (centeredCube z R hR),
        Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G u ≤
        liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop := by
    intro uN u hweak
    exact aux_prop_killed_inverse_moscoS S a G EN hEN hMoscoLower uN u hweak
  obtain ⟨EForm, hEForm, hHNC⟩ :=
    prop_killed_inverse_dirichlet_form (Q := centeredCube z R hR) S a G hSymm hPos hInj hroot
      ⟨hMoscoS, hMoscoRecov⟩ hcontract
  have hDens :=
    prop_killed_inverse_form_density (Q := centeredCube z R hR) G hroot EForm hEForm hHNC
      D hDcount hDdense hDsmooth
  refine ⟨G, ?_, ?_⟩
  · exact ⟨⟨hTend, hComp, hSymm, hPos, hInj⟩, hroot, ⟨EForm, hEForm, hHNC⟩,
      ⟨hMoscoLower, hMoscoRecov⟩, hDens⟩
  · intro y hy
    apply huniq y
    exact ⟨⟨hy.1.1, hy.1.2.1, hy.1.2.2.1, hy.1.2.2.2.1⟩,
      ⟨hy.2.2.2.1.1, hy.2.2.2.1.2⟩⟩

end Paper

