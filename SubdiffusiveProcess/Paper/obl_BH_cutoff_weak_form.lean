module

public import SubdiffusiveProcess.Paper.obl_BH_smooth_null_cutoffs
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Paper.prop_killed_inverse

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

namespace Paper


theorem aux_obl_BH_cutoff_weak_form_vc_memLp {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))) (vc : SpatialCoordinates d → ℝ)
    (hrep : (⇑v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc) :
    MemLp vc 2 (volume.restrict (Q : Set (SpatialCoordinates d))) := by
  exact MemLp.ae_eq hrep (Lp.memLp (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))))

theorem aux_obl_BH_cutoff_weak_form_primitive (K : Set ℝ) (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ)
    (hphi : ∀ n : ℕ, ContDiff ℝ ∞ (phi n) ∧ (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
      (∀ x ∈ K, phi n x = 1) ∧ tsupport (phi n) ⊆ U n) :
    ∃ T : ℕ → ℝ → ℝ, (∀ (n : ℕ) (t : ℝ), T n t = ∫ s in (0:ℝ)..t, phi n s) ∧
      (∀ n, T n 0 = 0 ∧ ∀ s t : ℝ, |T n s - T n t| ≤ |s - t|) := by
  refine ⟨fun n t => ∫ x in (0:ℝ)..t, phi n x, ?_, ?_⟩
  · intro n t; rfl
  · intro n
    have hc : Continuous (phi n) := (hphi n).1.continuous
    refine ⟨?_, ?_⟩
    · show ∫ x in (0:ℝ)..0, phi n x = 0
      exact intervalIntegral.integral_same
    · intro s t
      show |(∫ x in (0:ℝ)..s, phi n x) - ∫ x in (0:ℝ)..t, phi n x| ≤ |s - t|
      have hsub : (∫ x in (0:ℝ)..s, phi n x) - ∫ x in (0:ℝ)..t, phi n x
          = ∫ x in t..s, phi n x :=
        intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (0:ℝ) s)
          (hc.intervalIntegrable (0:ℝ) t)
      rw [hsub]
      calc |∫ x in t..s, phi n x| = ‖∫ x in t..s, phi n x‖ := (Real.norm_eq_abs _).symm
        _ ≤ 1 * |s - t| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
              rw [Real.norm_eq_abs, abs_of_nonneg ((hphi n).2.1 x).1]
              exact ((hphi n).2.1 x).2)
        _ = |s - t| := by rw [one_mul]

theorem aux_obl_BH_cutoff_weak_form_contract {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hnc : E.HasNormalContractions)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))) (hv : v ∈ E.domain)
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : (⇑v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc)
    (T : ℕ → ℝ → ℝ) (hTcont : ∀ n, Continuous (T n))
    (hT : ∀ n, DirichletForm.IsNormalContraction (T n)) :
    ∃ w : ℕ → Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))),
      ∀ n, w n ∈ E.domain ∧
        (⇑(w n) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (fun x => T n (vc x)) ∧
        E.form (w n) (w n) ≤ E.form v v := by
  classical
  have hmem : ∀ n : ℕ,
      MemLp (fun x => T n (vc x)) 2 (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    intro n
    have hvLp : MemLp (vc : SpatialCoordinates d → ℝ) 2
        (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      MemLp.ae_eq hrep (Lp.memLp v)
    have hle : ∀ x : SpatialCoordinates d, ‖T n (vc x)‖ ≤ ‖vc x‖ := by
      intro x
      have h := (hT n).dist_le (vc x) 0
      rw [(hT n).map_zero] at h
      simpa using h
    exact MemLp.of_le hvLp ((hTcont n).comp hvc).aestronglyMeasurable
      (Filter.Eventually.of_forall hle)
  refine ⟨fun n => (hmem n).toLp (fun x => T n (vc x)), ?_⟩
  intro n
  have hv_eq : (⇑((hmem n).toLp (fun x => T n (vc x)))) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T n (v x)) := by
    filter_upwards [MemLp.coeFn_toLp (hmem n), hrep] with x hx hxx
    rw [hx, hxx]
  have hres := hnc.operatesOn (T n) (hT n) v hv ((hmem n).toLp (fun x => T n (vc x))) hv_eq
  refine ⟨hres.1, ?_, hres.2⟩
  exact MemLp.coeFn_toLp (hmem n)

theorem aux_obl_BH_cutoff_weak_form_1
    {d : ℕ}
    {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hnc : DirichletForm.HasNormalContractions E)
    (K : Set ℝ)
    (U : ℕ → Set ℝ)
    (phi : ℕ → ℝ → ℝ)
    (hU : ∀ n : ℕ,
      IsOpen (U n) ∧ K ⊆ U n ∧
        volume.real (U n) ≤ 1 / ((n : ℝ) + 1))
    (hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤)
    (hphi : ∀ n : ℕ,
      ContDiff ℝ ∞ (phi n) ∧
        (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
        (∀ x ∈ K, phi n x = 1) ∧
        tsupport (phi n) ⊆ U n)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : Continuous vc)
    (hrep : (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc))
    (T : ℕ → ℝ → ℝ)
    (T_def : T = fun (n : ℕ) (t : ℝ) => ∫ (s : ℝ) in OfNat.ofNat (nat_lit 0)..t, phi n s)
    (hT_def : ∀ (n : ℕ) (t : ℝ), T n t = ∫ (s : ℝ) in OfNat.ofNat (nat_lit 0)..t, phi n s)
    (hT0 : ∀ (n : ℕ), T n (OfNat.ofNat (nat_lit 0)) = OfNat.ofNat (nat_lit 0)) :
    ∀ (n : ℕ), DirichletForm.IsNormalContraction (T n) := by
  intro n
  refine ⟨hT0 n, ?_⟩
  intro s t
  rw [hT_def n s, hT_def n t]
  have hcont : Continuous (phi n) := (hphi n).1.continuous
  have hsub : (∫ (x : ℝ) in (0 : ℝ)..s, phi n x) - ∫ (x : ℝ) in (0 : ℝ)..t, phi n x
      = ∫ (x : ℝ) in t..s, phi n x :=
    intervalIntegral.integral_interval_sub_left
      (hcont.intervalIntegrable 0 s) (hcont.intervalIntegrable 0 t)
  rw [hsub]
  have hle : ∀ x ∈ uIoc t s, ‖phi n x‖ ≤ (1 : ℝ) := by
    intro x _
    have h0 : 0 ≤ phi n x := ((hphi n).2.1 x).1
    have h1 : phi n x ≤ 1 := ((hphi n).2.1 x).2
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := phi n) (a := t) (b := s) (C := (1 : ℝ)) hle
  simpa using hint

theorem aux_obl_BH_cutoff_weak_form_2
    {d : ℕ}
    {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hnc : DirichletForm.HasNormalContractions E)
    (K : Set ℝ)
    (U : ℕ → Set ℝ)
    (phi : ℕ → ℝ → ℝ)
    (hU : ∀ n : ℕ,
      IsOpen (U n) ∧ K ⊆ U n ∧
        volume.real (U n) ≤ 1 / ((n : ℝ) + 1))
    (hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤)
    (hphi : ∀ n : ℕ,
      ContDiff ℝ ∞ (phi n) ∧
        (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
        (∀ x ∈ K, phi n x = 1) ∧
        tsupport (phi n) ⊆ U n)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvc : Continuous vc)
    (hrep : (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc))
    (T : ℕ → ℝ → ℝ)
    (T_def : T = fun (n : ℕ) (t : ℝ) => ∫ (s : ℝ) in OfNat.ofNat (nat_lit 0)..t, phi n s)
    (hT_def : ∀ (n : ℕ) (t : ℝ), T n t = ∫ (s : ℝ) in OfNat.ofNat (nat_lit 0)..t, phi n s)
    (hT0 : ∀ (n : ℕ), T n (OfNat.ofNat (nat_lit 0)) = OfNat.ofNat (nat_lit 0))
    (hT_nc : ∀ (n : ℕ), DirichletForm.IsNormalContraction (T n))
    (hTlip : ∀ (n : ℕ) (s t : ℝ), |T n s - T n t| ≤ |s - t|)
    (hoperates : ∀ (n : ℕ), E.OperatesOn (T n)) :
    ∀ (n : ℕ), ∃ w ∈ E.domain, (w.val.cast =ᶠ[ae (volume.restrict (SetLike.coe Q))] fun (x : SpatialCoordinates d) => T n (vc x)) ∧ E.form w w ≤ E.form v v := by
  intro n
  have hTnc : DirichletForm.IsNormalContraction (T n) := hT_nc n
  have hlip : LipschitzWith 1 (T n) := hTnc.lipschitzWith
  have hmemv : MemLp (fun x : SpatialCoordinates d => v x) 2
      (volume.restrict (Q : Set (SpatialCoordinates d))) := Lp.memLp v
  have hmem : MemLp (fun x : SpatialCoordinates d => T n (v x)) 2
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    hlip.comp_memLp (hT0 n) hmemv
  let w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    hmem.toLp (fun x : SpatialCoordinates d => T n (v x))
  have hcoe : (⇑w : SpatialCoordinates d → ℝ) = w.val.cast := rfl
  have hwae : (⇑w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T n (v x)) := hmem.coeFn_toLp
  have hcomp : (fun x : SpatialCoordinates d => T n (v x)) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T n (vc x)) := by
    filter_upwards [hrep] with x hx
    exact congrArg (T n) hx
  have hwvc : (⇑w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T n (vc x)) := hwae.trans hcomp
  obtain ⟨hwdom, hwle⟩ := hoperates n v hv w hwae
  refine ⟨w, hwdom, ?_, hwle⟩
  exact hwvc

theorem aux_obl_BH_cutoff_weak_form_vc_integrable
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : ⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc) :
    Integrable (fun x => (vc x) ^ 2) (volume.restrict (Q : Set (SpatialCoordinates d))) := by
  have hv : Integrable (fun x => (v : SpatialCoordinates d → ℝ) x ^ 2)
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    (Lp.memLp v).integrable_sq
  refine hv.congr ?_
  filter_upwards [hrep] with x hx
  rw [hx]

theorem aux_obl_BH_cutoff_weak_form_markov_w
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hnc : DirichletForm.HasNormalContractions E)
    (K : Set ℝ) (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ)
    (hU : ∀ n : ℕ, IsOpen (U n) ∧ K ⊆ U n ∧ volume.real (U n) ≤ 1 / ((n : ℝ) + 1))
    (hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤)
    (hphi : ∀ n : ℕ, ContDiff ℝ ∞ (phi n) ∧ (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧ (∀ x ∈ K, phi n x = 1) ∧ tsupport (phi n) ⊆ U n)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : ⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc) :
    ∀ n : ℕ, ∃ w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))),
      w ∈ E.toClosedForm.domain ∧
        (⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (fun x => ∫ s in (0 : ℝ)..(vc x), phi n s)) ∧
        E.toClosedForm.form w w ≤ E.toClosedForm.form v v := by
  intro n
  let T : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, phi n s
  have hncT : DirichletForm.IsNormalContraction T := by
    refine ⟨by simp [T], ?_⟩
    intro s t
    have hcont : Continuous (phi n) := (hphi n).1.continuous
    have hsub : T s - T t = ∫ x in t..s, phi n x := by
      dsimp only [T]
      rw [intervalIntegral.integral_interval_sub_left (f := phi n) (a := 0) (b := s) (c := t)
        (hcont.intervalIntegrable 0 s) (hcont.intervalIntegrable 0 t)]
    have hb : ‖∫ x in t..s, phi n x‖ ≤ 1 * |s - t| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x => phi n x)
        (a := t) (b := s) (C := 1) (fun x _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg ((hphi n).2.1 x).1]
          exact ((hphi n).2.1 x).2)
    rw [hsub]
    have hb' : |∫ x in t..s, phi n x| ≤ 1 * |s - t| := by
      simpa [Real.norm_eq_abs] using hb
    linarith
  have hmLp : MeasureTheory.MemLp (fun x : SpatialCoordinates d => T (v x)) 2
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    have hTlip : LipschitzWith 1 T := DirichletForm.IsNormalContraction.lipschitzWith hncT
    simpa only [Function.comp_apply] using! hTlip.comp_memLp hncT.map_zero (Lp.memLp v)
  let u : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    hmLp.toLp (fun x : SpatialCoordinates d => T (v x))
  have hu_rep : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => T (v x) :=
    hmLp.coeFn_toLp
  have hu_dom : u ∈ E.domain := (hnc.operatesOn T hncT v hv u hu_rep).1
  have hu_form : E.form u u ≤ E.form v v := (hnc.operatesOn T hncT v hv u hu_rep).2
  refine ⟨u, hu_dom, ?_, hu_form⟩
  refine hu_rep.trans ?_
  filter_upwards [hrep] with x hx
  rw [hx]

theorem aux_obl_BH_cutoff_weak_form_prim_lipschitz
    (phi : ℕ → ℝ → ℝ)
    (hphi : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) :
    ∀ n : ℕ, ∀ t : ℝ, |∫ s in (0 : ℝ)..t, phi n s| ≤ |t| := by
  intro n t
  have hmain : ‖∫ s in (0 : ℝ)..t, phi n s‖ ≤ 1 * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (f := phi n)
      (a := (0 : ℝ)) (b := t) (C := 1) ?_
    intro x hx
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hphi n x).1], (hphi n x).2⟩
  simpa [Real.norm_eq_abs] using hmain

theorem aux_obl_BH_cutoff_weak_form_prim_vanish_bound_fin
    (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ)
    (hU : ∀ n : ℕ, IsOpen (U n) ∧ volume.real (U n) ≤ 1 / ((n : ℝ) + 1))
    (hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤)
    (hphi : ∀ n : ℕ, ContDiff ℝ ∞ (phi n) ∧ (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧ tsupport (phi n) ⊆ U n) :
    ∀ n : ℕ, ∀ t : ℝ, |∫ s in (0 : ℝ)..t, phi n s| ≤ 1 / ((n : ℝ) + 1) := by
  intro n t
  have hcont : Continuous (phi n) := (hphi n).1.continuous
  have hmeas : MeasurableSet (U n) := (hU n).1.measurableSet
  have hfin : volume (U n) ≠ ⊤ := hUfinite n
  have hbound : ∀ a b : ℝ, a ≤ b → |∫ s in a..b, phi n s| ≤ volume.real (U n) := by
    intro a b hab
    have h3 : ∫ s in (Set.Ioc a b), |phi n s| ∂volume ≤ volume.real (U n) := by
      set s : Set ℝ := Set.Ioc a b with hsdef
      set s' : Set ℝ := s ∩ U n with hs'def
      set s'' : Set ℝ := s \ U n with hs''def
      have hs_meas : MeasurableSet s := by rw [hsdef]; exact measurableSet_Ioc
      have hs'_meas : MeasurableSet s' := by rw [hs'def]; exact hs_meas.inter hmeas
      have hs''_meas : MeasurableSet s'' := by rw [hs''def]; exact hs_meas.diff hmeas
      have hdisj : Disjoint s' s'' := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact hx2.2 hx1.2
      have hunion : s' ∪ s'' = s := by
        ext x
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, hs'def, hs''def]
        tauto
      have hf_int : IntegrableOn (fun x => |phi n x|) s := by
        rw [hsdef]; exact hcont.abs.integrableOn_Ioc
      have hf_int' : IntegrableOn (fun x => |phi n x|) s' :=
        hf_int.mono_set Set.inter_subset_left
      have hf_int'' : IntegrableOn (fun x => |phi n x|) s'' :=
        hf_int.mono_set Set.diff_subset
      have hunion_int := setIntegral_union hdisj hs''_meas hf_int' hf_int''
      have hEqOn : Set.EqOn (fun x => |phi n x|) (fun _ => (0 : ℝ)) s'' := by
        intro x hx
        show |phi n x| = 0
        have hxU : x ∉ U n := hx.2
        have hxts : x ∉ tsupport (phi n) := fun hc => hxU ((hphi n).2.2 hc)
        rw [image_eq_zero_of_notMem_tsupport hxts, abs_zero]
      have hzero : ∫ x in s'', |phi n x| ∂volume = 0 := by
        rw [setIntegral_congr_fun hs''_meas hEqOn, integral_zero]
      have hfin_s' : volume s' < ⊤ :=
        lt_of_le_of_lt (measure_mono (show s' ⊆ U n from Set.inter_subset_right))
          (lt_top_iff_ne_top.mpr hfin)
      have hptw : ∀ x ∈ s', ‖|phi n x|‖ ≤ (1 : ℝ) := by
        intro x hx
        have h0 : 0 ≤ phi n x := ((hphi n).2.1 x).1
        have h1 : phi n x ≤ 1 := ((hphi n).2.1 x).2
        rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (phi n x)), abs_of_nonneg h0]
        exact h1
      have hbound' : ∫ x in s', |phi n x| ∂volume ≤ volume.real s' := by
        have h := norm_setIntegral_le_of_norm_le_const (μ := volume) hfin_s' hptw
        rw [Real.norm_eq_abs, one_mul] at h
        exact (abs_le.mp h).2
      have hsplit :
          ∫ x in s, |phi n x| ∂volume
            = ∫ x in s', |phi n x| ∂volume + ∫ x in s'', |phi n x| ∂volume := by
        rw [← hunion_int, hunion]
      rw [hsplit]
      calc ∫ x in s', |phi n x| ∂volume + ∫ x in s'', |phi n x| ∂volume
          ≤ volume.real s' + 0 := add_le_add hbound' (le_of_eq hzero)
        _ = volume.real s' := add_zero _
        _ ≤ volume.real (U n) :=
            measureReal_mono (show s' ⊆ U n from Set.inter_subset_right) hfin
    calc |∫ s in a..b, phi n s| ≤ ∫ s in a..b, |phi n s| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ s in (Set.Ioc a b), |phi n s| ∂volume := intervalIntegral.integral_of_le hab
      _ ≤ volume.real (U n) := h3
  by_cases ht : 0 ≤ t
  · exact le_trans (hbound 0 t ht) (hU n).2
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hsym : |∫ s in 0..t, phi n s| = |∫ s in t..0, phi n s| := by
      rw [intervalIntegral.integral_symm (f := phi n) 0 t, abs_neg]
    rw [hsym]
    exact le_trans (hbound t 0 ht') (hU n).2

theorem aux_obl_BH_cutoff_weak_form_L2_vanish_norm_2
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ)
    (hU : ∀ n : ℕ, IsOpen (U n) ∧ volume.real (U n) ≤ 1 / ((n : ℝ) + 1))
    (hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤)
    (hphi : ∀ n : ℕ, ContDiff ℝ ∞ (phi n) ∧ (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧ tsupport (phi n) ⊆ U n)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc))
    (T : ℕ → ℝ → ℝ) (hT : ∀ n : ℕ, ∀ t : ℝ, T n t = ∫ s in (0 : ℝ)..t, phi n s)
    (w : ℕ → Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hw : ∀ n : ℕ, (⇑(w n) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (fun x => T n (vc x))))
    (hbound : ∀ n : ℕ, ∀ t : ℝ, |T n t| ≤ 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n : ℕ => ‖w n‖) atTop (𝓝 0) := by
  have hvcmem : MemLp vc 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    MemLp.ae_eq hrep (Lp.memLp v)
  have hvc2 : Integrable (fun x : SpatialCoordinates d => vc x ^ 2)
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    hvcmem.integrable_sq
  have hTab : ∀ (n : ℕ) (t : ℝ), |T n t| ≤ |t| := by
    intro n t
    rw [hT n t]
    have hbnd : ∀ x ∈ uIoc (0 : ℝ) t, ‖phi n x‖ ≤ 1 := by
      intro x _
      rw [Real.norm_eq_abs, abs_of_nonneg ((hphi n).2.1 x).1]
      exact ((hphi n).2.1 x).2
    calc |∫ s in (0 : ℝ)..t, phi n s| = ‖∫ s in (0 : ℝ)..t, phi n s‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ 1 * |t - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      _ = |t| := by rw [sub_zero, one_mul]
  have hpt : ∀ x : SpatialCoordinates d,
      Tendsto (fun n : ℕ => (T n (vc x)) ^ 2) atTop (𝓝 0) := by
    intro x
    have htend : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have habs : Tendsto (fun n : ℕ => |T n (vc x)|) atTop (𝓝 0) :=
      squeeze_zero (fun n => abs_nonneg _) (fun n => hbound n (vc x)) htend
    have h0 : Tendsto (fun n : ℕ => T n (vc x)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [Real.norm_eq_abs] using habs
    simpa using h0.pow 2
  have hI : Tendsto
      (fun n : ℕ => ∫ x, (T n (vc x)) ^ 2
        ∂(volume.restrict (Q : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
    have hdc := tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (Q : Set (SpatialCoordinates d)))
        (F := fun n (x : SpatialCoordinates d) => (T n (vc x)) ^ 2)
        (f := fun _ : SpatialCoordinates d => (0 : ℝ))
        (fun x : SpatialCoordinates d => vc x ^ 2)
        (fun n => ((Lp.memLp (w n)).aestronglyMeasurable.congr (hw n)).pow 2)
        hvc2
        (fun n => Filter.Eventually.of_forall (fun x : SpatialCoordinates d => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hh := mul_self_le_mul_self (abs_nonneg (T n (vc x))) (hTab n (vc x))
          rw [← sq, ← sq, sq_abs, sq_abs] at hh
          exact hh))
        (Filter.Eventually.of_forall hpt)
    simpa using hdc
  have hnorm : ∀ n : ℕ, ‖w n‖ = Real.sqrt
      (∫ x, (T n (vc x)) ^ 2
        ∂(volume.restrict (Q : Set (SpatialCoordinates d)))) := by
    intro n
    have hgmem : MemLp (fun x : SpatialCoordinates d => T n (vc x)) 2
        (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      MemLp.ae_eq (hw n) (Lp.memLp (w n))
    have hn1 : ‖w n‖ = (eLpNorm (fun x : SpatialCoordinates d => T n (vc x)) 2
        (volume.restrict (Q : Set (SpatialCoordinates d)))).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (hw n)]
    rw [hn1, hgmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    rw [show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) by norm_num]
    have hint : (∫ a, ‖T n (vc a)‖ ^ (2 : ℝ)
          ∂(volume.restrict (Q : Set (SpatialCoordinates d)))) =
        ∫ a, (T n (vc a)) ^ 2
          ∂(volume.restrict (Q : Set (SpatialCoordinates d))) := by
      apply integral_congr_ae
      filter_upwards with a
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [hint, Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
  have hsqrt : Tendsto
      (fun n : ℕ => Real.sqrt (∫ x, (T n (vc x)) ^ 2
        ∂(volume.restrict (Q : Set (SpatialCoordinates d))))) atTop (𝓝 0) := by
    have h := hI.sqrt
    simpa using h
  exact hsqrt.congr' (Filter.Eventually.of_forall (fun n => (hnorm n).symm))



namespace WeakNull

variable {X : Type*} [MeasurableSpace X] {m : Measure X} (E : _root_.DirichletForm.ClosedForm m)

noncomputable section

private def EnergySpace : Type _ := E.domain

private instance energyAddCommGroup : AddCommGroup (EnergySpace E) :=
  inferInstanceAs (AddCommGroup E.domain)

private instance energyModule : Module ℝ (EnergySpace E) :=
  inferInstanceAs (Module ℝ E.domain)

private def energyCore : InnerProductSpace.Core ℝ (EnergySpace E) where
  inner x y := E.form x.1 y.1 + inner ℝ x.1 y.1
  conj_inner_symm x y := by
    change E.form y.1 x.1 + inner ℝ y.1 x.1 =
      E.form x.1 y.1 + inner ℝ x.1 y.1
    rw [E.form_symm y.1 y.2 x.1 x.2, real_inner_comm]
  re_inner_nonneg x := by
    change 0 ≤ E.form x.1 x.1 + inner ℝ x.1 x.1
    rw [real_inner_self_eq_norm_sq]
    exact add_nonneg (E.form_nonneg x.1 x.2) (sq_nonneg _)
  add_left x y z := by
    change E.form (x.1 + y.1) z.1 + inner ℝ (x.1 + y.1) z.1 =
      (E.form x.1 z.1 + inner ℝ x.1 z.1) +
        (E.form y.1 z.1 + inner ℝ y.1 z.1)
    rw [E.form_add_left x.1 x.2 y.1 y.2 z.1 z.2, inner_add_left]
    ring
  smul_left x y c := by
    change E.form (c • x.1) y.1 + inner ℝ (c • x.1) y.1 =
      c * (E.form x.1 y.1 + inner ℝ x.1 y.1)
    rw [E.form_smul_left c x.1 x.2 y.1 y.2, real_inner_smul_left, mul_add]
  definite x hx := by
    change E.form x.1 x.1 + inner ℝ x.1 x.1 = 0 at hx
    rw [real_inner_self_eq_norm_sq] at hx
    have hsq : ‖x.1‖ ^ 2 = 0 := by
      apply le_antisymm
      · linarith [E.form_nonneg x.1 x.2]
      · exact sq_nonneg _
    have hxnorm : ‖x.1‖ = 0 :=
      mul_self_eq_zero.mp (by simpa only [pow_two] using hsq)
    apply Subtype.ext
    change x.1 = 0
    exact norm_eq_zero.mp hxnorm

private instance energyNormedAddCommGroup : NormedAddCommGroup (EnergySpace E) :=
  @InnerProductSpace.Core.toNormedAddCommGroup
    ℝ (EnergySpace E) _ _ _ (energyCore E)

private instance energyInnerProductSpace : InnerProductSpace ℝ (EnergySpace E) :=
  InnerProductSpace.ofCore (energyCore E).toCore

private theorem energy_inner (x y : EnergySpace E) :
    inner ℝ x y = E.form x.1 y.1 + inner ℝ x.1 y.1 := rfl

private theorem energy_norm_sq (x : EnergySpace E) :
    ‖x‖ ^ 2 = E.form x.1 x.1 + ‖x.1‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
    _ = E.form x.1 x.1 + ‖x.1‖ ^ 2 := by
      rw [energy_inner, real_inner_self_eq_norm_sq]

private theorem energy_norm (x : EnergySpace E) :
    ‖x‖ = Real.sqrt (E.form x.1 x.1 + ‖x.1‖ ^ 2) := by
  rw [← energy_norm_sq E x, Real.sqrt_sq (norm_nonneg x)]

private theorem ambient_norm_le_energy_norm (x : EnergySpace E) :
    ‖x.1‖ ≤ ‖x‖ := by
  calc
    ‖x.1‖ = Real.sqrt (‖x.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x.1)).symm
    _ ≤ Real.sqrt (E.form x.1 x.1 + ‖x.1‖ ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_left (E.form_nonneg x.1 x.2))
    _ = ‖x‖ := (energy_norm E x).symm

private theorem square_strict_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 2 < b ^ 2 := by
  have hprod : 0 < (b - a) * (b + a) :=
    mul_pos (sub_pos.mpr hab) (by linarith)
  nlinarith

private instance energyCompleteSpace : CompleteSpace (EnergySpace E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro z hz
  have hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form ((z p).1 - (z q).1) ((z p).1 - (z q).1) +
        ‖(z p).1 - (z q).1‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hz)
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨N, ?_⟩
    intro p hp q hq
    have hn : ‖z p - z q‖ < Real.sqrt ε := by
      simpa only [dist_eq_norm] using hN p hp q hq
    have hs := square_strict_mono_nonneg (norm_nonneg (z p - z q)) hn
    rw [Real.sq_sqrt hε.le] at hs
    calc
      E.form ((z p).1 - (z q).1) ((z p).1 - (z q).1) +
          ‖(z p).1 - (z q).1‖ ^ 2 = ‖z p - z q‖ ^ 2 :=
        (energy_norm_sq E (z p - z q)).symm
      _ < ε := hs
  obtain ⟨v, hv, hlim⟩ := E.complete
    (fun n => (z n).1) (fun n => (z n).2) hc
  let z₀ : EnergySpace E := ⟨v, hv⟩
  refine ⟨z₀, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hsq : Tendsto (fun n => ‖z n - z₀‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [energy_norm_sq] using! hlim
  have hsqrt : Tendsto (fun n => Real.sqrt (‖z n - z₀‖ ^ 2))
      atTop (𝓝 (Real.sqrt (0 : ℝ))) :=
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

private def energyInclusion : EnergySpace E →L[ℝ] Lp ℝ 2 m :=
  ({ toFun := fun x => x.1
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : EnergySpace E →ₗ[ℝ] Lp ℝ 2 m).mkContinuous
    1 (by
      intro x
      simpa only [one_mul] using! ambient_norm_le_energy_norm E x)

private theorem energyInclusion_apply (x : EnergySpace E) :
    energyInclusion E x = x.1 := rfl

private theorem energyInclusion_injective : Function.Injective (energyInclusion E) := by
  intro x y h
  apply Subtype.ext
  exact h

private theorem dense_adjoint_range_of_injective
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (i : H →L[ℝ] K) (hi : Function.Injective i) :
    Dense (Set.range (ContinuousLinearMap.adjoint i)) := by
  let S : Submodule ℝ H := LinearMap.range (ContinuousLinearMap.adjoint i).toLinearMap
  have hperp : S.orthogonal = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hzero : inner ℝ ((ContinuousLinearMap.adjoint i) (i x)) x = 0 :=
        hx _ ⟨i x, rfl⟩
      have hself : inner ℝ (i x) (i x) = 0 := by
        simpa only [ContinuousLinearMap.adjoint_inner_left] using hzero
      have hix : i x = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hself
      rw [Submodule.mem_bot]
      apply hi
      simpa only [map_zero] using hix
    · exact bot_le
  have hclosure : S.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr hperp
  change Dense (S : Set H)
  rw [dense_iff_closure_eq]
  change (S.topologicalClosure : Set H) = Set.univ
  exact congrArg (fun T : Submodule ℝ H => (T : Set H)) hclosure

private theorem inner_tendsto_zero_of_injective
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (i : H →L[ℝ] K) (hi : Function.Injective i)
    (v : ℕ → H) (B : ℝ) (hB : 0 < B)
    (hbounded : ∀ᶠ n in atTop, ‖v n‖ ≤ B)
    (hsmall : Tendsto (fun n => ‖i (v n)‖) atTop (𝓝 0)) (u : H) :
    Tendsto (fun n => inner ℝ u (v n)) atTop (𝓝 0) := by
  have hd := dense_adjoint_range_of_injective i hi
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨f, hf⟩ := (Metric.mem_closure_range_iff.mp (hd u))
    ((ε / 2) / B) (div_pos (half_pos hε) hB)
  have happrox : ‖u - (ContinuousLinearMap.adjoint i) f‖ * B < ε / 2 := by
    apply (lt_div_iff₀ hB).mp
    simpa only [dist_eq_norm] using hf
  have hadjoint : Tendsto
      (fun n => inner ℝ ((ContinuousLinearMap.adjoint i) f) (v n))
      atTop (𝓝 0) := by
    have hambient : Tendsto (fun n => inner ℝ f (i (v n))) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => norm_inner_le_norm (𝕜 := ℝ) f (i (v n)))
      simpa only [mul_zero] using hsmall.const_mul ‖f‖
    simpa only [ContinuousLinearMap.adjoint_inner_left] using hambient
  have heventually : ∀ᶠ n in atTop,
      ‖inner ℝ ((ContinuousLinearMap.adjoint i) f) (v n)‖ < ε / 2 := by
    simpa only [dist_zero_right] using
      (Metric.tendsto_nhds.mp hadjoint) (ε / 2) (half_pos hε)
  filter_upwards [hbounded, heventually] with n hn hfn
  have herror : ‖inner ℝ (u - (ContinuousLinearMap.adjoint i) f) (v n)‖ < ε / 2 := by
    calc
      ‖inner ℝ (u - (ContinuousLinearMap.adjoint i) f) (v n)‖
          ≤ ‖u - (ContinuousLinearMap.adjoint i) f‖ * ‖v n‖ :=
        norm_inner_le_norm (𝕜 := ℝ) _ _
      _ ≤ ‖u - (ContinuousLinearMap.adjoint i) f‖ * B :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ < ε / 2 := happrox
  have hsplit : inner ℝ u (v n) =
      inner ℝ (u - (ContinuousLinearMap.adjoint i) f) (v n) +
        inner ℝ ((ContinuousLinearMap.adjoint i) f) (v n) := by
    rw [inner_sub_left, sub_add_cancel]
  rw [dist_zero_right, hsplit]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem aux_weak_null_form_tendsto_zero
    (w : ℕ → Lp ℝ 2 m) (hw : ∀ n, w n ∈ E.domain) (C : ℝ)
    (hbdd : ∀ n, E.form (w n) (w n) ≤ C)
    (hnorm : Tendsto (fun n => ‖w n‖) atTop (𝓝 0))
    (u : Lp ℝ 2 m) (hu : u ∈ E.domain) :
    Tendsto (fun n => E.form u (w n)) atTop (𝓝 0) := by
  let v : ℕ → EnergySpace E := fun n => ⟨w n, hw n⟩
  let uH : EnergySpace E := ⟨u, hu⟩
  have hC : 0 ≤ C := (E.form_nonneg (w 0) (hw 0)).trans (hbdd 0)
  let B : ℝ := Real.sqrt (C + 1)
  have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
  have hunit : ∀ᶠ n in atTop, ‖w n‖ < 1 :=
    hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbounded : ∀ᶠ n in atTop, ‖v n‖ ≤ B := by
    filter_upwards [hunit] with n hn
    rw [energy_norm]
    apply Real.sqrt_le_sqrt
    change E.form (w n) (w n) + ‖w n‖ ^ 2 ≤ C + 1
    have hs : ‖w n‖ ^ 2 < (1 : ℝ) ^ 2 :=
      square_strict_mono_nonneg (norm_nonneg (w n)) hn
    nlinarith [hbdd n]
  have hsmall : Tendsto (fun n => ‖energyInclusion E (v n)‖)
      atTop (𝓝 0) := by
    simpa only [energyInclusion_apply] using hnorm
  have hH : Tendsto (fun n => inner ℝ uH (v n)) atTop (𝓝 0) :=
    inner_tendsto_zero_of_injective (energyInclusion E)
      (energyInclusion_injective E) v B hB hbounded hsmall uH
  have hL2 : Tendsto (fun n => inner ℝ u (w n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => norm_inner_le_norm (𝕜 := ℝ) u (w n))
    simpa only [mul_zero] using hnorm.const_mul ‖u‖
  have hdiff := hH.sub hL2
  change Tendsto
    (fun n => (E.form u (w n) + inner ℝ u (w n)) - inner ℝ u (w n))
    atTop (𝓝 ((0 : ℝ) - 0)) at hdiff
  simpa only [add_sub_cancel_right, sub_self] using hdiff

end

end WeakNull



theorem aux_obl_BH_cutoff_weak_form_weak_null
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (w : ℕ → Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hwdom : ∀ n : ℕ, w n ∈ E.toClosedForm.domain)
    (hbdd : ∀ n : ℕ, E.toClosedForm.form (w n) (w n) ≤ E.toClosedForm.form v v)
    (hnorm : Tendsto (fun n : ℕ => ‖w n‖) atTop (𝓝 0))
    (u : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hu : u ∈ E.toClosedForm.domain) :
    Tendsto (fun n : ℕ => E.toClosedForm.form u (w n)) atTop (𝓝 0) :=
  WeakNull.aux_weak_null_form_tendsto_zero E.toClosedForm w hwdom
    (E.toClosedForm.form v v) hbdd hnorm u hu



theorem obl_BH_cutoff_weak_form
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hnc : DirichletForm.HasNormalContractions E)
    (K : Set ℝ)
    (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ)
    (hU : ∀ n : ℕ,
      IsOpen (U n) ∧ K ⊆ U n ∧
        volume.real (U n) ≤ 1 / ((n : ℝ) + 1))
    (hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤)
    (hphi : ∀ n : ℕ,
      ContDiff ℝ ∞ (phi n) ∧
        (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
        (∀ x ∈ K, phi n x = 1) ∧
        tsupport (phi n) ⊆ U n)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc)) :
    ∃ (T : ℕ → ℝ → ℝ)
      (w : ℕ → Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
      (∀ n : ℕ, ∀ t : ℝ,
        T n t = ∫ s in (0 : ℝ)..t, phi n s) ∧
      (∀ n : ℕ, T n 0 = 0 ∧
        ∀ s t : ℝ, |T n s - T n t| ≤ |s - t|) ∧
      (∀ n : ℕ,
        w n ∈ E.toClosedForm.domain ∧
          (⇑(w n) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => T n (vc x)))) ∧
      (∀ n : ℕ,
        E.toClosedForm.form (w n) (w n) ≤ E.toClosedForm.form v v) ∧
      Tendsto (fun n : ℕ => ‖w n‖) atTop (𝓝 0) ∧
      (∀ u : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))),
        u ∈ E.toClosedForm.domain →
          Tendsto (fun n : ℕ => E.toClosedForm.form u (w n)) atTop (𝓝 0)) := by
  obtain ⟨T, hT1, hT2⟩ := aux_obl_BH_cutoff_weak_form_primitive K U phi hphi
  choose w hw using
    aux_obl_BH_cutoff_weak_form_markov_w E hnc K U phi hU hUfinite hphi v hv vc hvc hrep
  have hU' : ∀ n : ℕ, IsOpen (U n) ∧ volume.real (U n) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => ⟨(hU n).1, (hU n).2.2⟩
  have hphi' : ∀ n : ℕ, ContDiff ℝ ∞ (phi n) ∧ (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
      tsupport (phi n) ⊆ U n :=
    fun n => ⟨(hphi n).1, (hphi n).2.1, (hphi n).2.2.2⟩
  have hae : ∀ n : ℕ, ⇑(w n) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T n (vc x)) := by
    intro n
    filter_upwards [(hw n).2.1] with x hx
    rw [hx, hT1]
  have hbound : ∀ n : ℕ, ∀ t : ℝ, |T n t| ≤ 1 / ((n : ℝ) + 1) := by
    intro n t
    rw [hT1]
    exact aux_obl_BH_cutoff_weak_form_prim_vanish_bound_fin U phi hU' hUfinite hphi' n t
  have hnorm : Tendsto (fun n : ℕ => ‖w n‖) atTop (𝓝 0) :=
    aux_obl_BH_cutoff_weak_form_L2_vanish_norm_2 U phi hU' hUfinite hphi' v vc hvc hrep T hT1 w
      hae hbound
  exact ⟨T, w, hT1, hT2, fun n => ⟨(hw n).1, hae n⟩, fun n => (hw n).2.2, hnorm,
    fun u hu => aux_obl_BH_cutoff_weak_form_weak_null E v w (fun n => (hw n).1)
      (fun n => (hw n).2.2) hnorm u hu⟩

end Paper
