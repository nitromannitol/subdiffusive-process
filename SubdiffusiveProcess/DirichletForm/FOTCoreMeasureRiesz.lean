module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureFunctional
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal RealInnerProductSpace CompactlySupported ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Continuous core representatives viewed in the supremum norm. -/
def tests (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) : Submodule ℝ (X →ᵇ ℝ) where
  carrier := {f | HasCompactSupport f ∧ tsupport f ⊆ U ∧
    ∃ v : Lp ℝ 2 m, v ∈ F.domain ∧ ⇑v =ᵐ[m] ⇑f}
  zero_mem' := by
    refine ⟨?_, ?_, 0, F.domain.zero_mem, ?_⟩
    · simp [HasCompactSupport, tsupport]
    · simp [tsupport]
    · exact Lp.coeFn_zero ℝ 2 m
  add_mem' := by
    rintro f g ⟨hfc, hfs, v, hv, hve⟩ ⟨hgc, hgs, w, hw, hwe⟩
    refine ⟨hfc.add hgc, ?_, v + w, F.domain.add_mem hv hw, ?_⟩
    · have hs : tsupport (f + g) ⊆ tsupport f ∪ tsupport g :=
        (closure_mono (Function.support_add f g)).trans closure_union.le
      exact hs.trans (union_subset hfs hgs)
    · exact (Lp.coeFn_add v w).trans (hve.add hwe)
  smul_mem' := by
    rintro c f ⟨hfc, hfs, v, hv, hve⟩
    refine ⟨hfc.smul_left, (tsupport_smul_subset_right (fun _ => c) f).trans hfs,
      c • v, F.domain.smul_mem c hv, ?_⟩
    exact (Lp.coeFn_smul c v).trans (hve.const_smul c)

local instance testNormed (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) :
    NormedAddCommGroup (tests F U) := (tests F U).normedAddCommGroup

local instance testNormedSpace (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) :
    NormedSpace ℝ (tests F U) := (tests F U).normedSpace

variable {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}

def testLp (f : tests F U) : Lp ℝ 2 m := Classical.choose f.property.2.2

theorem testLp_mem (f : tests F U) : testLp f ∈ F.domain :=
  (Classical.choose_spec f.property.2.2).1

theorem testLp_ae (f : tests F U) : ⇑(testLp f) =ᵐ[m] ⇑f.1 :=
  (Classical.choose_spec f.property.2.2).2

theorem testLp_core (f : tests F U) : F.toClosedForm.MemCoreOn U (testLp f) :=
  ⟨testLp_mem f, f.1, f.1.continuous, f.property.1, f.property.2.1, testLp_ae f⟩

theorem testLp_bound (f : tests F U) : ∀ᵐ x ∂m, |testLp f x| ≤ ‖f.1‖ := by
  filter_upwards [testLp_ae f] with x hx
  rw [hx, ← Real.norm_eq_abs]
  exact f.1.norm_coe_le_norm x

theorem testLp_add (f g : tests F U) : testLp (f + g) = testLp f + testLp g := by
  apply Lp.ext
  exact (testLp_ae (f + g)).trans ((Lp.coeFn_add _ _).trans ((testLp_ae f).add (testLp_ae g))).symm

theorem testLp_smul (c : ℝ) (f : tests F U) : testLp (c • f) = c • testLp f := by
  apply Lp.ext
  exact (testLp_ae (c • f)).trans ((Lp.coeFn_smul _ _).trans ((testLp_ae f).const_smul c)).symm

/-- A compactly supported continuous function is a bounded continuous function. -/
def bounded (f : C_c(X, ℝ)) : X →ᵇ ℝ := (f : C₀(X, ℝ)).toBCF

omit [MeasurableSpace X] in
@[simp] theorem bounded_apply
    {X : Type*} [_portSection1 : MeasurableSpace X] [_portSection2 : TopologicalSpace X] (f : C_c(X, ℝ)) (x : X) : bounded f x = f x := rfl

omit [MeasurableSpace X] in
theorem bounded_add
    {X : Type*} [_portSection1 : MeasurableSpace X] [_portSection2 : TopologicalSpace X] (f g : C_c(X, ℝ)) : bounded (f + g) = bounded f + bounded g := rfl

omit [MeasurableSpace X] in
theorem bounded_smul
    {X : Type*} [_portSection1 : MeasurableSpace X] [_portSection2 : TopologicalSpace X] (c : ℝ) (f : C_c(X, ℝ)) : bounded (c • f) = c • bounded f := rfl

/-- Concrete bounded-core data, obtained from the core representative and the product theorem. -/
structure Input (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) (u : Lp ℝ 2 m) where
  core : F.toClosedForm.MemCoreOn U u
  rep : X → ℝ
  rep_cont : Continuous rep
  rep_compact : HasCompactSupport rep
  rep_support : tsupport rep ⊆ U
  rep_ae : ⇑u =ᵐ[m] rep
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bound_ae : ∀ᵐ x ∂m, |u x| ≤ bound
  square : Lp ℝ 2 m
  square_mem : square ∈ F.domain
  square_ae : ⇑square =ᵐ[m] fun x => u x ^ 2

variable {u : Lp ℝ 2 m}

theorem input_exists (hu : F.toClosedForm.MemCoreOn U u) : Nonempty (Input F U u) := by
  obtain ⟨M, hM⟩ := ae_abs_le_of_memCoreOn hu
  have hb : ∀ᵐ x ∂m, |u x| ≤ max 0 M := hM.mono fun x hx => hx.trans (le_max_right _ _)
  obtain ⟨w, hw, hae⟩ := exists_mul_mem F hu.1 hu.1 hb hb
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := hu.2
  exact ⟨⟨hu, f, hf, hfc, hfU, hfae, max 0 M, le_max_left _ _, hb,
    w, hw, by simpa [sq] using hae⟩⟩

def productLp (a : Input F U u) (f : tests F U) : Lp ℝ 2 m :=
  Classical.choose (exists_mul_mem F a.core.1 (testLp_mem f)
    (a.bound_ae.mono fun _x hx => hx.trans (le_max_left a.bound ‖f.1‖))
    ((testLp_bound f).mono fun _x hx => hx.trans (le_max_right a.bound ‖f.1‖)))

theorem productLp_mem (a : Input F U u) (f : tests F U) : productLp a f ∈ F.domain :=
  (Classical.choose_spec (exists_mul_mem F a.core.1 (testLp_mem f)
    (a.bound_ae.mono fun _x hx => hx.trans (le_max_left a.bound ‖f.1‖))
    ((testLp_bound f).mono fun _x hx => hx.trans (le_max_right a.bound ‖f.1‖)))).1

theorem productLp_ae (a : Input F U u) (f : tests F U) :
    ⇑(productLp a f) =ᵐ[m] fun x => u x * f.1 x := by
  have hp := (Classical.choose_spec (exists_mul_mem F a.core.1 (testLp_mem f)
    (a.bound_ae.mono fun x hx => hx.trans (le_max_left a.bound ‖f.1‖))
    ((testLp_bound f).mono fun x hx => hx.trans (le_max_right a.bound ‖f.1‖)))).2
  change ⇑(productLp a f) =ᵐ[m] fun x => u x * testLp f x at hp
  filter_upwards [hp, testLp_ae f] with x h1 h2
  rw [h1, h2]

theorem productLp_add (a : Input F U u) (f g : tests F U) :
    productLp a (f + g) = productLp a f + productLp a g := by
  apply Lp.ext
  filter_upwards [productLp_ae a (f + g), Lp.coeFn_add (productLp a f) (productLp a g),
    productLp_ae a f, productLp_ae a g] with x h1 h2 h3 h4
  simp only [h1, h2, Pi.add_apply, h3, h4]
  change u x * (f.1 x + g.1 x) = u x * f.1 x + u x * g.1 x
  ring

theorem productLp_smul (a : Input F U u) (c : ℝ) (f : tests F U) :
    productLp a (c • f) = c • productLp a f := by
  apply Lp.ext
  filter_upwards [productLp_ae a (c • f), Lp.coeFn_smul c (productLp a f),
    productLp_ae a f] with x h1 h2 h3
  simp only [h1, h2, Pi.smul_apply, smul_eq_mul, h3]
  change u x * (c * f.1 x) = c * (u x * f.1 x)
  ring

def linear (a : Input F U u) : tests F U →ₗ[ℝ] ℝ where
  toFun f := F.form u (productLp a f) - (1 / 2 : ℝ) * F.form a.square (testLp f)
  map_add' f g := by
    rw [productLp_add, testLp_add,
      F.toClosedForm.form_add_right a.core.1 (productLp_mem a f) (productLp_mem a g),
      F.toClosedForm.form_add_right a.square_mem (testLp_mem f) (testLp_mem g)]
    ring
  map_smul' c f := by
    rw [productLp_smul, testLp_smul,
      F.toClosedForm.form_smul_right c a.core.1 (productLp_mem a f),
      F.toClosedForm.form_smul_right c a.square_mem (testLp_mem f)]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

theorem linear_bound (h : Data F U) (a : Input F U u) (f : tests F U) :
    ‖linear a f‖ ≤ F.form u u * ‖f‖ := by
  have hp : ⇑(productLp a f) =ᵐ[m] fun x => u x * testLp f x := by
    filter_upwards [productLp_ae a f, testLp_ae f] with x h1 h2
    rw [h1, h2]
  simpa only [linear, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, mul_comm] using!
    core_functional_bound F h a.core (testLp_core f) (norm_nonneg f.1) (testLp_bound f)
      (productLp_mem a f) a.square_mem hp a.square_ae

def functional (h : Data F U) (a : Input F U u) : tests F U →L[ℝ] ℝ := by
  exact LinearMap.mkContinuous (E := tests F U) (F := ℝ) (linear a)
    (F.form u u) (linear_bound h a)

theorem functional_nonneg (h : Data F U) (a : Input F U u) (f : tests F U)
    (hf : ∀ x, 0 ≤ f.1 x) : 0 ≤ functional h a f := by
  have hp : ⇑(productLp a f) =ᵐ[m] fun x => u x * testLp f x := by
    filter_upwards [productLp_ae a f, testLp_ae f] with x h1 h2
    rw [h1, h2]
  change 0 ≤ F.form u (productLp a f) - (1 / 2 : ℝ) * F.form a.square (testLp f)
  apply core_functional_nonneg F h a.core (testLp_core f) _
    (productLp_mem a f) a.square_mem hp a.square_ae
  filter_upwards [testLp_ae f] with x hx
  rw [hx]
  exact hf x

def globalFunctional (h : Data F U) (a : Input F U u) : (X →ᵇ ℝ) →L[ℝ] ℝ :=
  Classical.choose (_root_.exists_extension_norm_eq (𝕜 := ℝ) (tests F U) (functional h a))

theorem globalFunctional_apply (h : Data F U) (a : Input F U u) (f : tests F U) :
    globalFunctional h a f.1 = functional h a f :=
  (Classical.choose_spec (_root_.exists_extension_norm_eq (𝕜 := ℝ) (tests F U) (functional h a))).1 f

theorem globalFunctional_norm_le (h : Data F U) (a : Input F U u) :
    ‖globalFunctional h a‖ ≤ F.form u u := by
  have he : ‖globalFunctional h a‖ = ‖functional h a‖ :=
    (Classical.choose_spec (_root_.exists_extension_norm_eq (𝕜 := ℝ) (tests F U) (functional h a))).2
  rw [he]
  exact LinearMap.mkContinuous_norm_le (E := tests F U) (F := ℝ) (linear a)
    (F.form_nonneg u a.core.1) (linear_bound h a)

structure Cutoff (a : Input F U u) where
  test : tests F U
  bounds : ∀ x, 0 ≤ test.1 x ∧ test.1 x ≤ 1
  plateau : Set X
  plateau_open : IsOpen plateau
  support_plateau : tsupport a.rep ⊆ plateau
  eq_one : ∀ x ∈ plateau, test.1 x = 1

theorem cutoff_exists [T2Space X] [LocallyCompactSpace X]
    (h : Data F U) (a : Input F U u) : Nonempty (Cutoff a) := by
  obtain ⟨C, hcore⟩ := h.core
  obtain ⟨v, f, V, hv, hf, hfc, hfU, hvae, h01, hV, hKV, h1⟩ :=
    hcore.exists_cutoff F a.rep_compact h.isOpen a.rep_support (Subset.rfl)
  let fc : C_c(X, ℝ) := ⟨⟨f, hf⟩, hfc⟩
  exact ⟨⟨⟨bounded fc, hfc, hfU, v, hv.1, hvae⟩, h01, V, hV, hKV, h1⟩⟩

theorem cutoff_functional (h : Data F U) (a : Input F U u) (χ : Cutoff a) :
    functional h a χ.test = F.form u u := by
  have hp : productLp a χ.test = u := by
    apply Lp.ext
    filter_upwards [productLp_ae a χ.test, a.rep_ae] with x hx hu
    rw [hx]
    by_cases hs : x ∈ tsupport a.rep
    · rw [χ.eq_one x (χ.support_plateau hs), mul_one]
    · rw [hu, image_eq_zero_of_notMem_tsupport hs, zero_mul]
  have hχ : ∃ K : Set X, IsCompact K ∧ K ⊆ U ∧
      ∀ᵐ x ∂m, x ∉ K → testLp χ.test x = 0 := by
    refine ⟨tsupport χ.test.1, χ.test.property.1, χ.test.property.2.1, ?_⟩
    filter_upwards [testLp_ae χ.test] with x hx hs
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport hs
  have hsq : ∃ K : Set X, IsCompact K ∧ K ⊆ U ∩ χ.plateau ∧
      ∀ᵐ x ∂m, x ∉ K → a.square x = 0 := by
    refine ⟨tsupport a.rep, a.rep_compact, subset_inter a.rep_support χ.support_plateau, ?_⟩
    filter_upwards [a.square_ae, a.rep_ae] with x hs hu hK
    rw [hs, hu, image_eq_zero_of_notMem_tsupport hK, zero_pow two_ne_zero]
  have hplateau : ∀ᵐ x ∂m, x ∈ χ.plateau → testLp χ.test x = 1 := by
    filter_upwards [testLp_ae χ.test] with x hx hV
    rw [hx]
    exact χ.eq_one x hV
  have hzero := h.stronglyLocal (testLp χ.test) (testLp_mem χ.test)
    a.square a.square_mem hχ 1 χ.plateau χ.plateau_open hsq hplateau
  have hzero' : F.form a.square (testLp χ.test) = 0 := by
    rw [F.form_symm a.square a.square_mem (testLp χ.test) (testLp_mem χ.test)]
    exact hzero
  change F.form u (productLp a χ.test) - (1 / 2 : ℝ) * F.form a.square (testLp χ.test) = _
  rw [hp, hzero', mul_zero, sub_zero]

def localized (h : Data F U) (a : Input F U u) (χ : Cutoff a) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := globalFunctional h a (bounded f * χ.test.1)
  map_add' f g := by
    rw [bounded_add, add_mul, map_add]
  map_smul' c f := by
    rw [bounded_smul, smul_mul_assoc, map_smul]
    rfl

theorem localized_nonneg (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    (f : C_c(X, ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ localized h a χ f := by
  let M := ‖bounded f‖
  have hM : 0 ≤ M := norm_nonneg _
  have hfb : ∀ x, f x ≤ M := fun x =>
    (le_abs_self (f x)).trans ((bounded f).norm_coe_le_norm x)
  let g := M • χ.test.1 - bounded f * χ.test.1
  have hg : ‖g‖ ≤ M := by
    apply (BoundedContinuousFunction.norm_le hM).mpr
    intro x
    change |M * χ.test.1 x - f x * χ.test.1 x| ≤ M
    have hχ := χ.bounds x
    have h0 : 0 ≤ M - f x := sub_nonneg.mpr (hfb x)
    have h1 : M - f x ≤ M := by linarith [hf x]
    rw [show M * χ.test.1 x - f x * χ.test.1 x = (M - f x) * χ.test.1 x by ring,
      abs_of_nonneg (mul_nonneg h0 hχ.1)]
    exact (mul_le_of_le_one_right h0 hχ.2).trans h1
  have hG : globalFunctional h a g ≤ F.form u u * M := by
    apply (le_abs_self _).trans
    apply ((globalFunctional h a).le_opNorm g).trans
    exact mul_le_mul (globalFunctional_norm_le h a) hg (norm_nonneg _)
      (F.form_nonneg u a.core.1)
  have hv : globalFunctional h a χ.test.1 = F.form u u :=
    (globalFunctional_apply h a χ.test).trans (cutoff_functional h a χ)
  change 0 ≤ globalFunctional h a (bounded f * χ.test.1)
  change globalFunctional h a (M • χ.test.1 - bounded f * χ.test.1) ≤ _ at hG
  rw [map_sub, map_smul, hv] at hG
  simp only [smul_eq_mul] at hG
  nlinarith

def positive (h : Data F U) (a : Input F U u) (χ : Cutoff a) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := localized h a χ
  monotone' := by
    intro f g hfg
    have hp := localized_nonneg h a χ (g - f) (fun x => sub_nonneg.mpr (hfg x))
    rw [map_sub] at hp
    exact sub_nonneg.mp hp

/-- Products of bounded continuous core tests are again core tests. -/
def testMul (f g : tests F U) : tests F U :=
  ⟨f.1 * g.1, f.property.1.mul_right, tsupport_mul_subset_left.trans f.property.2.1, by
    obtain ⟨w, hw, hae⟩ := exists_mul_mem F (testLp_mem f) (testLp_mem g)
      ((testLp_bound f).mono fun x hx => hx.trans (le_max_left ‖f.1‖ ‖g.1‖))
      ((testLp_bound g).mono fun x hx => hx.trans (le_max_right ‖f.1‖ ‖g.1‖))
    refine ⟨w, hw, ?_⟩
    filter_upwards [hae, testLp_ae f, testLp_ae g] with x h1 h2 h3
    simpa only [h2, h3] using! h1⟩

@[simp] theorem testMul_val (f g : tests F U) : (testMul f g).1 = f.1 * g.1 := rfl

def testCompact (f : tests F U) : C_c(X, ℝ) := ⟨f.1.toContinuousMap, f.property.1⟩

@[simp] theorem bounded_testCompact (f : tests F U) : bounded (testCompact f) = f.1 := by
  ext x
  rfl

theorem functional_mul_cutoff (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    (f : tests F U) : functional h a (testMul f χ.test) = functional h a f := by
  have hp : productLp a (testMul f χ.test) = productLp a f := by
    apply Lp.ext
    filter_upwards [productLp_ae a (testMul f χ.test), productLp_ae a f,
      a.rep_ae] with x h1 h2 hu
    rw [h1, h2]
    change u x * (f.1 x * χ.test.1 x) = u x * f.1 x
    by_cases hs : x ∈ tsupport a.rep
    · rw [χ.eq_one x (χ.support_plateau hs), mul_one]
    · rw [hu, image_eq_zero_of_notMem_tsupport hs, zero_mul, zero_mul]
  let z := testLp f - testLp (testMul f χ.test)
  have hz := F.domain.sub_mem (testLp_mem f) (testLp_mem (testMul f χ.test))
  have hzcore := testLp_core (f - testMul f χ.test)
  have hsub : testLp (f - testMul f χ.test) = z := by
    apply Lp.ext
    exact (testLp_ae _).trans ((Lp.coeFn_sub _ _).trans
      ((testLp_ae f).sub (testLp_ae (testMul f χ.test)))).symm
  rw [hsub] at hzcore
  have hKz : ∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∀ᵐ x ∂m, x ∉ K → z x = 0 := by
    obtain ⟨zf, hzf, hzfc, hzfU, hzae⟩ := hzcore.2
    refine ⟨tsupport zf, hzfc, hzfU, ?_⟩
    filter_upwards [hzae] with x hx hK
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport hK
  have hKs : ∃ K : Set X, IsCompact K ∧ K ⊆ U ∩ χ.plateau ∧
      ∀ᵐ x ∂m, x ∉ K → a.square x = 0 := by
    refine ⟨tsupport a.rep, a.rep_compact, subset_inter a.rep_support χ.support_plateau, ?_⟩
    filter_upwards [a.square_ae, a.rep_ae] with x h1 h2 hK
    rw [h1, h2, image_eq_zero_of_notMem_tsupport hK, zero_pow two_ne_zero]
  have hz0 : ∀ᵐ x ∂m, x ∈ χ.plateau → z x = 0 := by
    filter_upwards [Lp.coeFn_sub (testLp f) (testLp (testMul f χ.test)),
      testLp_ae f, testLp_ae (testMul f χ.test)] with x h1 h2 h3 hx
    change (testLp f - testLp (testMul f χ.test)) x = 0
    rw [h1, Pi.sub_apply, h2, h3]
    change f.1 x - f.1 x * χ.test.1 x = 0
    rw [χ.eq_one x hx, mul_one, sub_self]
  have he := h.stronglyLocal z hz a.square a.square_mem hKz 0 χ.plateau
    χ.plateau_open hKs hz0
  have he' : F.form a.square (testLp f) = F.form a.square (testLp (testMul f χ.test)) := by
    rw [F.form_symm z hz a.square a.square_mem,
      F.toClosedForm.form_sub_right a.square_mem (testLp_mem f)
        (testLp_mem (testMul f χ.test))] at he
    exact sub_eq_zero.mp he
  change F.form u (productLp a (testMul f χ.test)) - _ = F.form u (productLp a f) - _
  rw [hp, he']

theorem localized_test (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    (f : tests F U) : positive h a χ (testCompact f) = functional h a f := by
  change globalFunctional h a (bounded (testCompact f) * χ.test.1) = _
  rw [bounded_testCompact]
  exact (globalFunctional_apply h a (testMul f χ.test)).trans (functional_mul_cutoff h a χ f)

section RieszMeasure
variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

def measure (h : Data F U) (a : Input F U u) (χ : Cutoff a) : Measure X :=
  RealRMK.rieszMeasure (positive h a χ)

instance measure_regular (h : Data F U) (a : Input F U u) (χ : Cutoff a) :
    (measure h a χ).Regular := RealRMK.regular_rieszMeasure _

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
theorem positive_le_energy
    {X : Type*} [_portSection1 : MeasurableSpace X] [_portSection2 : TopologicalSpace X] {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {u : ↥(Lp ℝ 2 m)} [_portSection7 : T2Space X] [_portSection8 : LocallyCompactSpace X] [_portSection9 : BorelSpace X] (h : Data F U) (a : Input F U u) (χ : Cutoff a)
    (f : C_c(X, ℝ)) (hf : ∀ x, |f x| ≤ 1) : positive h a χ f ≤ F.form u u := by
  have hb : ‖bounded f * χ.test.1‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro x
    change |f x * χ.test.1 x| ≤ 1
    rw [abs_mul, abs_of_nonneg (χ.bounds x).1]
    exact (mul_le_of_le_one_left (χ.bounds x).1 (hf x)).trans (χ.bounds x).2
  exact (le_abs_self _).trans (((globalFunctional h a).le_opNorm _).trans
    ((mul_le_mul (globalFunctional_norm_le h a) hb (norm_nonneg _)
      (F.form_nonneg u a.core.1)).trans_eq (mul_one _)))

theorem measure_mass (h : Data F U) (a : Input F U u) (χ : Cutoff a) :
    measure h a χ univ = ENNReal.ofReal (F.form u u) := by
  apply le_antisymm
  · rw [isOpen_univ.measure_eq_iSup_isCompact (measure h a χ)]
    refine iSup_le fun K => iSup_le fun _ => iSup_le fun hK => ?_
    obtain ⟨f, hf1, hfc, hfU, h01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
    let fc : C_c(X, ℝ) := ⟨f, hfc⟩
    exact (RealRMK.rieszMeasure_le_of_eq_one (positive h a χ)
      (f := fc) (fun x => (h01 x).1) hK hf1).trans
        (ENNReal.ofReal_le_ofReal (positive_le_energy h a χ fc
          (fun x => by change |f x| ≤ 1; rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2)))
  · rw [← cutoff_functional h a χ, ← localized_test h a χ χ.test]
    exact RealRMK.le_rieszMeasure_tsupport_subset (positive h a χ) χ.bounds (subset_univ _)

instance measure_finite (h : Data F U) (a : Input F U u) (χ : Cutoff a) :
    IsFiniteMeasure (measure h a χ) := ⟨by rw [measure_mass]; exact ENNReal.ofReal_lt_top⟩

end RieszMeasure

end SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz
