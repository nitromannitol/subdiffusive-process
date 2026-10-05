module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowCompetitorOscillation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowSummationBoundaryCellPrice

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The translated parent is the translate of the origin cube at the same
scale. -/
theorem translateSet_neg_translatedCube (d : ℕ) (k : ℤ) (c : Vec d) :
    translateSet (-c) (translatedCube d k c) = openCubeSet (originCube d k) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Section6ExcessDecay.mem_translatedCube_iff]
  constructor
  · intro hx
    have : x - -c - c = x := by abel
    simpa [cube, this] using hx
  · intro hx
    have : x - -c - c = x := by abel
    simpa [cube, this] using hx

/-- An `H¹₀` function on the origin cube, transported to a translate of that
cube. -/
def stepRowTranslateH10 (k : ℤ) (c : Vec d)
    (r : H10Function (openCubeSet (originCube d k))) :
    H10Function (translatedCube d k c) :=
  H10Function.untranslate (-c)
    (castH10Domain (translateSet_neg_translatedCube d k c).symm r)

omit [NeZero d] in
@[simp] theorem stepRowTranslateH10_toFun (k : ℤ) (c : Vec d)
    (r : H10Function (openCubeSet (originCube d k))) (x : Vec d) :
    (stepRowTranslateH10 k c r).toH1Function.toFun x =
      r.toH1Function.toFun (x - c) := by
  have hx : x + -c = x - c := by abel
  simp [stepRowTranslateH10, hx]

omit [NeZero d] in
@[simp] theorem stepRowTranslateH10_grad (k : ℤ) (c : Vec d)
    (r : H10Function (openCubeSet (originCube d k))) (x : Vec d) :
    (stepRowTranslateH10 k c r).toH1Function.grad x =
      r.toH1Function.grad (x - c) := by
  have hx : x + -c = x - c := by abel
  simp [stepRowTranslateH10, hx]

omit [NeZero d] in
/-- **The glued residual.**

From the Dirichlet zero-trace witness of `u − h` on `𝔠_m` and any `H¹₀` datum
correction `r` on the origin cube of the parent's scale, the function

```text
rho = (u − h) − ext(r(· − c))
```

is a genuine `H¹₀(𝔠_m)` function whose value and gradient on the projected
parent are those of `u − h − r(· − c)` — that is, of `u − v` when `r` is the
competitor's own zero-trace difference.  Off the parent it is `u − h`. -/
theorem exists_stepRowResidualCorrector {m : ℕ} {k : ℤ} {c : Vec d}
    (hPsub : translatedCube d k c ⊆ cube d (m : ℤ))
    {u h : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (hzt : HasZeroTraceDifferenceOn (openCubeSet (originCube d (m : ℤ))) u h)
    (r : H10Function (openCubeSet (originCube d k))) :
    ∃ rho : H10Function (openCubeSet (originCube d (m : ℤ))),
      (∀ p ∈ translatedCube d k c,
          rho.toH1Function.toFun p =
            u.toFun p - h.toFun p - r.toH1Function.toFun (p - c)) ∧
        (∀ p ∈ translatedCube d k c,
          rho.toH1Function.grad p =
            u.grad p - h.grad p - r.toH1Function.grad (p - c)) ∧
        (∀ p ∉ translatedCube d k c,
          rho.toH1Function.toFun p = u.toFun p - h.toFun p) ∧
        (∀ p ∉ translatedCube d k c,
          rho.toH1Function.grad p = u.grad p - h.grad p) := by
  obtain ⟨w, hwval, hwgrad⟩ := hzt
  have hPmeas : MeasurableSet (translatedCube d k c) :=
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d k
      c).isOpen.measurableSet
  have hVopen : IsOpen (openCubeSet (originCube d (m : ℤ))) :=
    isOpen_openCubeSet (originCube d (m : ℤ))
  have hPsub' : translatedCube d k c ⊆ openCubeSet (originCube d (m : ℤ)) := by
    simpa [cube] using hPsub
  set rT : H10Function (translatedCube d k c) := stepRowTranslateH10 k c r with hrT
  set rExt : H10Function (openCubeSet (originCube d (m : ℤ))) :=
    rT.extendByZeroToOpenSuperset hPmeas hVopen hPsub' with hrExt
  have hval : ∀ p : Vec d, (w - rExt).toH1Function.toFun p =
      w.toH1Function.toFun p - rT.zeroExtension p := by
    intro p
    change (w.toH1Function - rExt.toH1Function).toFun p = _
    simp only [H1Function.sub_toFun, hrExt,
      H10Function.extendByZeroToOpenSuperset_toFun]
  have hgrd : ∀ p : Vec d, (w - rExt).toH1Function.grad p =
      w.toH1Function.grad p - rT.zeroExtensionGrad p := by
    intro p
    change (w.toH1Function - rExt.toH1Function).grad p = _
    simp only [H1Function.sub_grad, hrExt,
      H10Function.extendByZeroToOpenSuperset_grad]
  refine ⟨w - rExt, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hval p, H10Function.zeroExtension_apply_of_mem rT hp, hrT,
      stepRowTranslateH10_toFun, hwval p]
    ring
  · intro p hp
    rw [hgrd p, H10Function.zeroExtensionGrad_apply_of_mem rT hp, hrT,
      stepRowTranslateH10_grad, hwgrad p]
    abel
  · intro p hp
    rw [hval p, H10Function.zeroExtension_apply_of_not_mem rT hp, hwval p]
    ring
  · intro p hp
    rw [hgrd p, H10Function.zeroExtensionGrad_apply_of_not_mem rT hp, hwgrad p]
    abel

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
