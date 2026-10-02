import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.AffineHarmonic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.ZeroTrace
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OddPackaging
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.BoundaryComposition




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory InnerProductSpace
open Homogenization (Vec H1Function MemH10 LocalizedZeroTraceFunctionOn volumeMeasureOn
  openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay (affineLift)

noncomputable section

variable {d : ℕ}

/-! ### The shifted competitor as an `H¹` function -/

/-- **The datum-split competitor** `V_odd = v − ℓ_h − v₁`, as an `H¹` function on
the window. -/
def datumSplitH1 {x : Vec d} {m k : ℤ} (v v₁ : H1Function (truncatedWindow x m k))
    (c : ℝ) (A : Vec d) : H1Function (truncatedWindow x m k) :=
  haveI : IsFiniteMeasure (volumeMeasureOn (truncatedWindow x m k)) :=
    (isOpenBoundedConvexDomain_truncatedWindow x m k).isFiniteMeasure_restrict_volume
  v - affineLiftH1
      (isOpenBoundedConvexDomain_truncatedWindow x m k).isSobolevRegularDomain x c A - v₁

@[simp] theorem datumSplitH1_toFun {x : Vec d} {m k : ℤ}
    (v v₁ : H1Function (truncatedWindow x m k)) (c : ℝ) (A : Vec d) :
    (datumSplitH1 v v₁ c A).toFun
      = fun y => v.toFun y - affineLift x c A y - v₁.toFun y := by
  haveI : IsFiniteMeasure (volumeMeasureOn (truncatedWindow x m k)) :=
    (isOpenBoundedConvexDomain_truncatedWindow x m k).isFiniteMeasure_restrict_volume
  funext y
  rw [datumSplitH1, Homogenization.H1Function.sub_toFun,
    Homogenization.H1Function.sub_toFun, affineLiftH1_toFun]

/-- **The datum-split competitor is weakly harmonic.**  `v` and `v₁` are by
hypothesis, and the affine lift is by `isUnitWeaklyHarmonicOn_affineLiftH1`. -/
theorem isUnitWeaklyHarmonicOn_datumSplitH1 {x : Vec d} {m k : ℤ}
    {v v₁ : H1Function (truncatedWindow x m k)}
    (hv : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hv₁ : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v₁) (c : ℝ) (A : Vec d) :
    IsUnitWeaklyHarmonicOn (truncatedWindow x m k) (datumSplitH1 v v₁ c A) := by
  haveI : IsFiniteMeasure (volumeMeasureOn (truncatedWindow x m k)) :=
    (isOpenBoundedConvexDomain_truncatedWindow x m k).isFiniteMeasure_restrict_volume
  exact isUnitWeaklyHarmonicOn_sub
    (isUnitWeaklyHarmonicOn_sub hv
      (isUnitWeaklyHarmonicOn_affineLiftH1
        (isOpenBoundedConvexDomain_truncatedWindow x m k).isSobolevRegularDomain x c A))
    hv₁

/-- **The datum-split competitor has face-only zero trace.**  This is
`ZeroTrace.localizedZeroTraceFunctionOn_datumSplit` read on the `H¹`
realization. -/
theorem localizedZeroTraceFunctionOn_datumSplitH1 {x : Vec d} {m k : ℤ}
    {u h : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvu : MemH10 (truncatedWindow x m k) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - affineLift x c A y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k)
      (datumSplitH1 v v₁ c A).toFun := by
  rw [datumSplitH1_toFun]
  exact localizedZeroTraceFunctionOn_datumSplit hdat hvu hΨ hv₁Ψ

/-! ### The classical competitor on the doubled window -/

/-- **The classical boundary competitor at the datum-split competitor, upper met
face.**

From the anchor's Dirichlet datum, the weak harmonicity of `v` and of the
corrector `v₁`, and the corrector's trace structure, the odd extension of
`V_odd = v − ℓ_h − v₁` across the met face is *classically* harmonic on the
doubled window `reflectedWindow x m k` — the `hharm` slot of
`Section6Schauder.exists_gradientHolder_boundary_truncatedCube`. -/
theorem exists_classicalCompetitor_datumSplit_of_meetsUpperFace [NeZero d] {x : Vec d}
    {m k : ℤ} (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    {u h : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvharm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hvu : MemH10 (truncatedWindow x m k) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hv₁harm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v₁)
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - affineLift x c A y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k) ∧
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m k) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (reflectedWindow x m k)]
        (fun y => oddFaceExtend ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
          (zeroExtend (truncatedWindow x m k)
            (fun p => v.toFun p - affineLift x c A p - v₁.toFun p)) y) := by
  obtain ⟨w, hwval, hwgrad⟩ :=
    exists_h1_oddFaceReflection_of_meetsUpperFace hkm hup hother (datumSplitH1 v v₁ c A)
      (localizedZeroTraceFunctionOn_datumSplitH1 hdat hvu hΨ hv₁Ψ)
  obtain ⟨V, hVR, hVW, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow_of_meetsUpperFace hkm hup hother
      (datumSplitH1 v v₁ c A) (isUnitWeaklyHarmonicOn_datumSplitH1 hvharm hv₁harm c A)
      w hwgrad
  refine ⟨V, hVR, hVW, hVmem, ?_⟩
  filter_upwards [hVae] with y hy
  rw [hy, hwval y, datumSplitH1_toFun]

/-- **The classical boundary competitor at the datum-split competitor, lower met
face.**  The lower-face twin of
`exists_classicalCompetitor_datumSplit_of_meetsUpperFace`. -/
theorem exists_classicalCompetitor_datumSplit_of_meetsLowerFace [NeZero d] {x : Vec d}
    {m k : ℤ} (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    {u h : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvharm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hvu : MemH10 (truncatedWindow x m k) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hv₁harm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v₁)
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - affineLift x c A y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k) ∧
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m k) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (reflectedWindow x m k)]
        (fun y => oddFaceExtend (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
          (zeroExtend (truncatedWindow x m k)
            (fun p => v.toFun p - affineLift x c A p - v₁.toFun p)) y) := by
  obtain ⟨w, hwval, hwgrad⟩ :=
    exists_h1_oddFaceReflection_of_meetsLowerFace hkm hlow hother (datumSplitH1 v v₁ c A)
      (localizedZeroTraceFunctionOn_datumSplitH1 hdat hvu hΨ hv₁Ψ)
  obtain ⟨V, hVR, hVW, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow_of_meetsLowerFace hkm hlow hother
      (datumSplitH1 v v₁ c A) (isUnitWeaklyHarmonicOn_datumSplitH1 hvharm hv₁harm c A)
      w hwgrad
  refine ⟨V, hVR, hVW, hVmem, ?_⟩
  filter_upwards [hVae] with y hy
  rw [hy, hwval y, datumSplitH1_toFun]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
