module

public import SubdiffusiveProcess.Paper.goodext_native_partition_bank
public import SubdiffusiveProcess.Compactness.FiniteUniformCover
public import SubdiffusiveProcess.Sobolev.UniformCubeLimit

@[expose] public section

/-! A finite compatible cubical partition has one glued Sobolev bank and a common
uniform subsequential limit on the parent cube. -/
open Filter MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- A finite compatible cubical partition has one continuous killed Sobolev bank and a common uniform subsequential limit. -/
theorem goodext_compact_native_partition_bank
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ) (hrad : ∀ i, 0 < rad i)
    (hsub : ∀ i, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hdisj : Pairwise (fun i j => Disjoint
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
      (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d))))
    (hcover : (⋃ i, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) =
      closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), g x = 0)
    (u : ∀ k : Fin m, ℕ →
      weakSobolevGraph (centeredCube (cent k) (rad k) (hrad k)))
    (U : Fin m → ℕ → SpatialCoordinates d → ℝ)
    (hcont : ∀ k n, ContinuousOn (U k n)
      (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))))
    (hrep : ∀ k n, ((u k n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))] U k n)
    (htrace : ∀ k n, ∀ x ∈ frontier
      (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)), U k n x = g x)
    (hcompact : ∀ k, ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ V : SpatialCoordinates d → ℝ,
        TendstoUniformlyOn (fun n => U k (sigma (tau n))) V atTop
          (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)))) :
    ∃ (w : ℕ → H10Function (centeredCube z R hR : Set (SpatialCoordinates d)))
      (sigma : ℕ → ℕ) (V : SpatialCoordinates d → ℝ)
      (v : DomainL2 (centeredCube z R hR)),
      StrictMono sigma ∧
      ContinuousOn V (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))] V ∧
      Tendsto (fun n => (sobolevDataOfH1 (w (sigma n)).toH1Function).1) atTop (𝓝 v) ∧
      TendstoUniformlyOn (fun n => (w (sigma n)).toH1Function.toFun) V atTop
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (∀ k, ∀ x ∈ frontier (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)),
        V x = g x) ∧
      ∀ n, ContinuousOn (w n).toH1Function.toFun
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
        ∀ k, EqOn (w n).toH1Function.toFun (U k n)
            (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))) ∧
          sobolevDataOfH1 ((w n).toH1Function.restrict
            (centeredCube (cent k) (rad k) (hrad k)).isOpen
            (hsub k)) = (u k n).val := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let Qc : Set (SpatialCoordinates d) := closure Q
  let X : Type := Qc
  let I : Type := Fin m
  let C : I → Set (SpatialCoordinates d) := fun k =>
    closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))
  let S : I → Set X := fun k => {x | (x : SpatialCoordinates d) ∈ C k}
  have hbank (n : ℕ) :
      ∃ w : H10Function Q,
        ContinuousOn w.toH1Function.toFun Qc ∧
        ∀ k, EqOn w.toH1Function.toFun (U k n) (C k) ∧
          sobolevDataOfH1 (w.toH1Function.restrict
            (centeredCube (cent k) (rad k) (hrad k)).isOpen (hsub k)) = (u k n).val := by
    exact goodext_native_partition_bank z R hR m cent rad hrad hsub hdisj hcover g hg0
      (fun k => u k n) (fun k => U k n) (fun k => hcont k n) (fun k => hrep k n)
      (fun k => htrace k n)
  let w : ℕ → H10Function Q := fun n => Classical.choose (hbank n)
  have hw (n : ℕ) :
      ContinuousOn (w n).toH1Function.toFun Qc ∧
      ∀ k, EqOn (w n).toH1Function.toFun (U k n) (C k) ∧
        sobolevDataOfH1 ((w n).toH1Function.restrict
          (centeredCube (cent k) (rad k) (hrad k)).isOpen (hsub k)) = (u k n).val :=
    Classical.choose_spec (hbank n)
  let f : ℕ → SpatialCoordinates d → ℝ := fun n x => (w n).toH1Function.toFun x
  let fX : ℕ → X → ℝ := fun n x => f n x
  have hcoverX : ∀ x : X, ∃ k : I, x ∈ S k := by
    intro x
    have hx : (x : SpatialCoordinates d) ∈
        ⋃ k : Fin m, closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)) := by
      rw [hcover]
      exact x.property
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨k, hk⟩
  have hfcont : ∀ n, Continuous (fX n) := by
    intro n
    exact continuousOn_iff_continuous_restrict.mp (hw n).1
  have hlocal : ∀ k : I, ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ G : X → ℝ,
        TendstoUniformlyOn (fun m => fX (sigma (tau m))) G atTop (S k) := by
    intro k sigma hsigma
    obtain ⟨tau, htau, G, hG⟩ := hcompact k sigma hsigma
    refine ⟨tau, htau, fun x => G x, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he := (Metric.tendstoUniformlyOn_iff.mp hG) ε hε
    filter_upwards [he] with m hm x hx
    have hxC : (x : SpatialCoordinates d) ∈ C k := hx
    have hEq : f (sigma (tau m)) (x : SpatialCoordinates d) =
        U k (sigma (tau m)) x := ((hw (sigma (tau m))).2 k).1 hxC
    simpa only [fX, f, hEq] using hm (x : SpatialCoordinates d) hxC
  obtain ⟨sigma, hsigma, G, hGcont, hG⟩ :=
    exists_uniform_subsequence_of_finite_cover S hcoverX fX hfcont hlocal
  let Gc : C(Qc, ℝ) := ⟨G, hGcont⟩
  obtain ⟨v, V, hVcont, hvV, hVeq⟩ := exists_cubeL2_of_continuous_closedCube z hR Gc
  have hlimV : TendstoUniformly
      (fun n (x : X) => fX (sigma n) x) (fun x => V x) atTop := by
    rw [Metric.tendstoUniformly_iff] at hG ⊢
    intro ε hε
    have he := hG ε hε
    filter_upwards [he] with n hn x
    have hEq : G x = V x := by
      change Gc x = V (x : SpatialCoordinates d)
      exact (hVeq x x.property).symm
    simpa only [hEq] using hn x
  let l2 : ℕ → DomainL2 (centeredCube z R hR) := fun n =>
    (sobolevDataOfH1 (w n).toH1Function).1
  have hl2rep (n : ℕ) : (l2 n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] f n := by
    exact sobolevDataOfH1_fst_coeFn (w n).toH1Function
  let fσ : ℕ → SpatialCoordinates d → ℝ := fun n => f (sigma n)
  let l2σ : ℕ → DomainL2 (centeredCube z R hR) := fun n => l2 (sigma n)
  have hl2σrep (n : ℕ) :
      (l2σ n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] fσ n :=
    hl2rep (sigma n)
  have hL2 : Tendsto l2σ atTop (𝓝 v) := by
    apply cube_tendsto_of_uniformly_on z hR fσ l2σ hl2σrep V v hvV
    simpa only [fX, fσ, f] using hlimV
  have hUniform : TendstoUniformlyOn (fun n => f (sigma n)) V atTop Qc := by
    rw [Metric.tendstoUniformlyOn_iff]
    rw [Metric.tendstoUniformly_iff] at hlimV
    intro ε hε
    have he := hlimV ε hε
    filter_upwards [he] with n hn x hx
    exact hn ⟨x, hx⟩
  have htraceV : ∀ k : I, ∀ x ∈ frontier
      (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)), V x = g x := by
    intro k x hx
    have hxC : x ∈ C k := frontier_subset_closure hx
    have hxQc : x ∈ Qc := closure_mono (hsub k) hxC
    have hpoint : ∀ n, f (sigma n) x = g x := by
      intro n
      calc
        f (sigma n) x = (w (sigma n)).toH1Function.toFun x := rfl
        _ = U k (sigma n) x := ((hw (sigma n)).2 k).1 hxC
        _ = g x := htrace k (sigma n) x hx
    have h1 : Tendsto (fun n => f (sigma n) x) atTop (𝓝 (V x)) :=
      hlimV.tendsto_at ⟨x, hxQc⟩
    have h2 : Tendsto (fun n : ℕ => g x) atTop (𝓝 (g x)) := tendsto_const_nhds
    have h3 : Tendsto (fun n => f (sigma n) x) atTop (𝓝 (g x)) := by
      simpa only [hpoint] using h2
    exact tendsto_nhds_unique h1 h3
  refine ⟨w, sigma, V, v, hsigma, hVcont, hvV, hL2, ?_, htraceV, ?_⟩
  · simpa only [f] using hUniform
  · intro n
    simpa only [Q, Qc, C] using hw n

end Paper
