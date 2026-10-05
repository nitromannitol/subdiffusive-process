module

public import SubdiffusiveProcess.Paper.prop_21_catalog_global_weighted_energy
public import SubdiffusiveProcess.Paper.prop_21_dual_energy_operator_unique
public import SubdiffusiveProcess.Paper.prop_21_full_cluster_convergence
public import SubdiffusiveProcess.Paper.prop_21_full_mosco
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_prop_21_signedIntegralOn_toSignedMeasure_sub
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : Set X) (_hB : MeasurableSet B) (f : X → ℝ)
    (hμ : Integrable f (μ.restrict B))
    (hν : Integrable f (ν.restrict B)) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn
        (μ.toSignedMeasure - ν.toSignedMeasure) B f =
      (∫ x in B, f x ∂μ) - (∫ x in B, f x ∂ν) := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn,
    Measure.toJordanDecomposition_toSignedMeasure_sub,
    Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
    Measure.jordanDecompositionOfToSignedMeasureSub_negPart]
  obtain ⟨s, hs, hνμ, hμν⟩ := MeasureTheory.exists_isHahnDecomposition ν μ
  have hμs : Integrable f ((μ.restrict s).restrict B) :=
    hμ.mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self B)
  have hμsc : Integrable f ((μ.restrict sᶜ).restrict B) :=
    hμ.mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self B)
  have hνs : Integrable f ((ν.restrict s).restrict B) :=
    hν.mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self B)
  have hνsc : Integrable f ((ν.restrict sᶜ).restrict B) :=
    hν.mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self B)
  have hμsplit : (μ.restrict s).restrict B + (μ.restrict sᶜ).restrict B = μ.restrict B := by
    have h := congrArg (fun m : Measure X => m.restrict B)
      (Measure.restrict_add_restrict_compl (μ := μ) hs)
    simpa only [Measure.restrict_add] using h
  have hνsplit : (ν.restrict s).restrict B + (ν.restrict sᶜ).restrict B = ν.restrict B := by
    have h := congrArg (fun m : Measure X => m.restrict B)
      (Measure.restrict_add_restrict_compl (μ := ν) hs)
    simpa only [Measure.restrict_add] using h
  have hδcomp : (μ - ν).restrict sᶜ = 0 := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hs.compl,
      Measure.sub_eq_zero_of_le hμν]
  have hηs : (ν - μ).restrict s = 0 := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hs,
      Measure.sub_eq_zero_of_le hνμ]
  have hδB : (μ - ν).restrict B = (μ.restrict s - ν.restrict s).restrict B := by
    calc
      (μ - ν).restrict B =
          ((μ - ν).restrict s).restrict B + ((μ - ν).restrict sᶜ).restrict B := by
        have h := congrArg (fun m : Measure X => m.restrict B)
          (Measure.restrict_add_restrict_compl (μ := μ - ν) hs)
        simpa only [Measure.restrict_add] using h.symm
      _ = ((μ - ν).restrict s).restrict B + 0 := by rw [hδcomp, Measure.restrict_zero]
      _ = ((μ - ν).restrict s).restrict B := add_zero _
      _ = (μ.restrict s - ν.restrict s).restrict B := by
        rw [Measure.restrict_sub_eq_restrict_sub_restrict hs]
  have hηB : (ν - μ).restrict B = (ν.restrict sᶜ - μ.restrict sᶜ).restrict B := by
    calc
      (ν - μ).restrict B =
          ((ν - μ).restrict s).restrict B + ((ν - μ).restrict sᶜ).restrict B := by
        have h := congrArg (fun m : Measure X => m.restrict B)
          (Measure.restrict_add_restrict_compl (μ := ν - μ) hs)
        simpa only [Measure.restrict_add] using h.symm
      _ = 0 + ((ν - μ).restrict sᶜ).restrict B := by rw [hηs, Measure.restrict_zero]
      _ = ((ν - μ).restrict sᶜ).restrict B := zero_add _
      _ = (ν.restrict sᶜ - μ.restrict sᶜ).restrict B := by
        rw [Measure.restrict_sub_eq_restrict_sub_restrict hs.compl]
  have hδs_int : Integrable f ((μ.restrict s - ν.restrict s).restrict B) :=
    hμs.mono_measure (Measure.restrict_mono_measure Measure.sub_le B)
  have hηsc_int : Integrable f ((ν.restrict sᶜ - μ.restrict sᶜ).restrict B) :=
    hνsc.mono_measure (Measure.restrict_mono_measure Measure.sub_le B)
  have hδadd : (μ.restrict s - ν.restrict s).restrict B +
      (ν.restrict s).restrict B = (μ.restrict s).restrict B := by
    have h := congrArg (fun m : Measure X => m.restrict B)
      (Measure.sub_add_cancel_of_le hνμ)
    simpa [Measure.restrict_add] using h
  have hηadd : (ν.restrict sᶜ - μ.restrict sᶜ).restrict B +
      (μ.restrict sᶜ).restrict B = (ν.restrict sᶜ).restrict B := by
    have h := congrArg (fun m : Measure X => m.restrict B)
      (Measure.sub_add_cancel_of_le hμν)
    simpa [Measure.restrict_add] using h
  have hδint : (∫ x in B, f x ∂(μ - ν)) =
      (∫ x in B, f x ∂(μ.restrict s)) -
        (∫ x in B, f x ∂(ν.restrict s)) := by
    have h := integral_add_measure hδs_int hνs
    rw [hδadd] at h
    rw [show (∫ x in B, f x ∂(μ - ν)) =
        ∫ x, f x ∂((μ - ν).restrict B) by rfl, hδB]
    change ∫ x, f x ∂((μ.restrict s - ν.restrict s).restrict B) = _
    linarith [h]
  have hηint : (∫ x in B, f x ∂(ν - μ)) =
      (∫ x in B, f x ∂(ν.restrict sᶜ)) -
        (∫ x in B, f x ∂(μ.restrict sᶜ)) := by
    have h := integral_add_measure hηsc_int hμsc
    rw [hηadd] at h
    rw [show (∫ x in B, f x ∂(ν - μ)) =
        ∫ x, f x ∂((ν - μ).restrict B) by rfl, hηB]
    change ∫ x, f x ∂((ν.restrict sᶜ - μ.restrict sᶜ).restrict B) = _
    linarith [h]
  have hμint := integral_add_measure hμs hμsc
  rw [hμsplit] at hμint
  have hνint := integral_add_measure hνs hνsc
  rw [hνsplit] at hνint
  rw [hδint, hηint]
  linarith

lemma aux_prop_21_signedIntegralOn_nonneg_smul
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (ν : SignedMeasure X) (c : ℝ) (hc : 0 ≤ c)
    (B : Set X) (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (c • ν) B f =
      c * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn,
    SignedMeasure.toJordanDecomposition_smul_real,
    JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
    JordanDecomposition.real_smul_negPart_nonneg _ _ hc]
  simp [Measure.restrict_smul, NNReal.smul_def, Real.coe_toNNReal', max_eq_left hc]
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]
  ring



theorem prop_21
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (S : ResponseSpace Q) (_hS : S.space = killedSobolevGraph Q)
    (a arho : ℕ → PositiveCoefficient Q)
    (E Erho : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE Grho : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy GE w)
    (hrhoform : ∀ w : DomainL2 Q, Erho.energy w = limitFormEnergy Grho w)
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x)
    (_hweight : ∀ (n : ℕ) (w : S.space),
      responseForm S (arho n) w w =
        ∫ x in (Q : Set (SpatialCoordinates d)),
          rho x * ((a n).val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2))
    (GrhoN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGrhoN : ∀ (n : ℕ) (f : DomainL2 Q), GrhoN n f =
      (responseSolution S (arho n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGrhoCluster : ∃ tau : ℕ → ℕ, StrictMono tau ∧
      Tendsto (fun n => GrhoN (tau n)) atTop (𝓝 Grho) ∧
      (∀ x y : DomainL2 Q, inner ℝ (Grho x) y = inner ℝ x (Grho y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (Grho x)))
    (hsubcluster : ∀ tau : ℕ → ℕ, StrictMono tau →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ (F : DomainL2 Q →L[ℝ] DomainL2 Q)
          (FForm : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
            (volume.restrict (Q : Set (SpatialCoordinates d))))
          (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure FForm),
          Tendsto (fun n => GrhoN (tau (sigma n))) atTop (𝓝 F) ∧
          (∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y)) ∧
          (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (F x)) ∧
          (∀ w : DomainL2 Q, FForm.energy w = limitFormEnergy F w) ∧
          limitFormDomain F = limitFormDomain GE ∧
          (∀ w : DomainL2 Q, MemFormCore GE w → w ∈ FForm.domain) ∧
          (∀ u ∈ limitFormDomain F, ∃ w : ℕ → S.space,
            Tendsto (fun n => ((w n).val.1,
              ((responseForm S (arho (tau (sigma n))) (w n) (w n) : ℝ) : EReal)))
              atTop (𝓝 (u, limitFormEnergy F u))) ∧
          (∀ (uN : ℕ → S.space) (u : DomainL2 Q),
            (∀ f : DomainL2 Q,
              Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
            limitFormEnergy F u ≤
              liminf (fun n =>
                ((responseForm S (arho (tau (sigma n))) (uN n) (uN n) : ℝ) : EReal))
                atTop) ∧
          (∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
            (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) →
            (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
            (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
              (Q : Set (SpatialCoordinates d)) →
            ∀ w : DomainL2 Q, MemFormCore GE w →
            ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
              B ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
              sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
                  (GammaE.measure w B).toReal ≤
                  (GammaF.measure w B).toReal ∧
                (GammaF.measure w B).toReal ≤
                  sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
                    (GammaE.measure w B).toReal))
    (hdense : ∀ w ∈ limitFormDomain GE, ∀ ε : ℝ, 0 < ε →
      ∃ p : DomainL2 Q, MemFormCore GE p ∧ ‖p - w‖ ≤ ε ∧
        limitFormEnergy GE (p - w) ≤ ((ε : ℝ) : EReal)) :
    -- (b) `D(E^rho) = D(E)`
    limitFormDomain Grho = limitFormDomain GE ∧
    -- (a) the full sequence `E_N^rho` Mosco-converges to `E^rho`
    (∀ u ∈ limitFormDomain Grho, ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm S (arho n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy Grho u))) ∧
    (∀ (uN : ℕ → S.space) (u : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy Grho u ≤
        liminf (fun n => ((responseForm S (arho n) (uN n) (uN n) : ℝ) : EReal))
          atTop) ∧
    -- (c) `eq:mfd-21`, on the diagonal and in the paper's bilinear form
    (∀ u ∈ limitFormDomain GE,
      limitFormEnergy Grho u =
        (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
          : EReal)) ∧
    (∀ u ∈ limitFormDomain GE, ∀ v ∈ limitFormDomain GE,
      Erho.form u v =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho) := by
  classical
  obtain ⟨tau0, htau0, hconv0, hGrhoSym, hGrhoPos⟩ := hGrhoCluster
  obtain ⟨sigma0, hsigma0, F0, FForm0, GammaF0, hconvF0, hF0sym, hF0pos,
    hF0form, hF0domainEq, hF0domain, hF0rec, hF0low, hF0measure⟩ :=
    hsubcluster tau0 htau0
  have hconvF0' : Tendsto (fun n => GrhoN (tau0 (sigma0 n))) atTop (𝓝 F0) :=
    hconvF0
  have hconvGrho0 : Tendsto (fun n => GrhoN (tau0 (sigma0 n))) atTop (𝓝 Grho) :=
    hconv0.comp hsigma0.tendsto_atTop
  have hF0eq : F0 = Grho := tendsto_nhds_unique hconvF0' hconvGrho0
  have hdomGrho : limitFormDomain Grho = limitFormDomain GE := by
    simpa [hF0eq] using hF0domainEq
  have hF0energy : ∀ u ∈ limitFormDomain GE,
      limitFormEnergy F0 u =
        (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
          : EReal) := by
    intro u hu
    exact prop_21_catalog_global_weighted_energy z0 R hR hQcube E FForm0 GE F0
      hEform hF0form GammaE GammaF0 rho hrhocont hrhopos hF0domainEq hF0domain
        hF0measure hdense u hu
  have hGrhoEnergy : ∀ u ∈ limitFormDomain GE,
      limitFormEnergy Grho u =
        (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
          : EReal) := by
    intro u hu
    simpa [hF0eq] using hF0energy u hu
  have hclusters : ∀ tau : ℕ → ℕ, StrictMono tau →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ F : DomainL2 Q →L[ℝ] DomainL2 Q,
          Tendsto (fun n => GrhoN (tau (sigma n))) atTop (𝓝 F) ∧
          (∀ u : DomainL2 Q, limitFormEnergy F u = limitFormEnergy Grho u) ∧
          (∀ x y : DomainL2 Q, inner ℝ (F x) y = inner ℝ x (F y)) ∧
          (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (F x)) := by
    intro tau htau
    obtain ⟨sigma, hsigma, F, FForm, GammaF, hconvF, hFsym, hFpos,
      hFform, hFdomainEq, hFdomain, hFrec, hFlow, hFmeasure⟩ :=
      hsubcluster tau htau
    have hFenergy : ∀ u ∈ limitFormDomain GE,
        limitFormEnergy F u =
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
            : EReal) := by
      intro u hu
      exact prop_21_catalog_global_weighted_energy z0 R hR hQcube E FForm GE F
        hEform hFform GammaE GammaF rho hrhocont hrhopos hFdomainEq hFdomain
          hFmeasure hdense u hu
    have henergy : ∀ u : DomainL2 Q,
        limitFormEnergy F u = limitFormEnergy Grho u := by
      intro u
      by_cases hu : u ∈ limitFormDomain GE
      · rw [hFenergy u hu, hGrhoEnergy u hu]
      · have huF : u ∉ limitFormDomain F := by
          rw [hFdomainEq]
          exact hu
        have huG : u ∉ limitFormDomain Grho := by
          rw [hdomGrho]
          exact hu
        have hFtop : limitFormEnergy F u = ⊤ := by
          exact le_antisymm le_top (not_lt.mp huF)
        have hGtop : limitFormEnergy Grho u = ⊤ := by
          exact le_antisymm le_top (not_lt.mp huG)
        exact hFtop.trans hGtop.symm
    exact ⟨sigma, hsigma, F, hconvF, henergy, hFsym, hFpos⟩
  have hconv : Tendsto GrhoN atTop (𝓝 Grho) :=
    prop_21_full_cluster_convergence GrhoN Grho hGrhoSym hGrhoPos hclusters
  have hmosco := prop_21_full_mosco S arho Grho GrhoN hGrhoN hGrhoSym hGrhoPos hconv
  have hbilinear : ∀ u ∈ limitFormDomain GE, ∀ v ∈ limitFormDomain GE,
      Erho.form u v =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho := by
    have mem_domain_of_energy_eq : ∀ (u : DomainL2 Q),
        Erho.energy u < (⊤ : EReal) → u ∈ Erho.domain := by
      intro u hu
      by_contra hnot
      have htop : Erho.energy u = (⊤ : EReal) := by
        simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy, hnot]
      exact (ne_of_lt hu) (by simp [htop])
    have hdiag : ∀ u ∈ limitFormDomain GE,
        Erho.form u u =
          ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u) := by
      intro u hu
      have huG : u ∈ limitFormDomain Grho := hdomGrho ▸ hu
      have huE : Erho.energy u < (⊤ : EReal) := by
        rw [hrhoform u]
        exact huG
      have huD : u ∈ Erho.domain := mem_domain_of_energy_eq u huE
      have he : ((Erho.form u u : ℝ) : EReal) =
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
            : EReal) := by
        calc
          ((Erho.form u u : ℝ) : EReal) = Erho.energy u := by
            simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy, huD]
          _ = limitFormEnergy Grho u := hrhoform u
          _ = (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
            : EReal) := hGrhoEnergy u hu
      exact_mod_cast he
    have mem_E_domain_of_energy_eq : ∀ (u : DomainL2 Q),
        E.energy u < (⊤ : EReal) → u ∈ E.domain := by
      intro u hu
      by_contra hnot
      have htop : E.energy u = (⊤ : EReal) := by
        simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy, hnot]
      exact (ne_of_lt hu) (by simp [htop])
    have hGE_add : ∀ u v : DomainL2 Q, u ∈ limitFormDomain GE →
        v ∈ limitFormDomain GE → u + v ∈ limitFormDomain GE := by
      intro u v hu hv
      have huE : u ∈ E.domain := mem_E_domain_of_energy_eq u (by
        rw [hEform u]
        exact hu)
      have hvE : v ∈ E.domain := mem_E_domain_of_energy_eq v (by
        rw [hEform v]
        exact hv)
      have huvE : u + v ∈ E.domain := E.domain.add_mem huE hvE
      change limitFormEnergy GE (u + v) < (⊤ : EReal)
      rw [← hEform (u + v)]
      simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy, huvE]
    have hGE_sub : ∀ u v : DomainL2 Q, u ∈ limitFormDomain GE →
        v ∈ limitFormDomain GE → u - v ∈ limitFormDomain GE := by
      intro u v hu hv
      have huE : u ∈ E.domain := mem_E_domain_of_energy_eq u (by
        rw [hEform u]
        exact hu)
      have hvE : v ∈ E.domain := mem_E_domain_of_energy_eq v (by
        rw [hEform v]
        exact hv)
      have huvE : u - v ∈ E.domain := E.domain.sub_mem huE hvE
      change limitFormEnergy GE (u - v) < (⊤ : EReal)
      rw [← hEform (u - v)]
      simp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy, huvE]
    intro u hu v hv
    have huG : u ∈ limitFormDomain Grho := hdomGrho ▸ hu
    have hvG : v ∈ limitFormDomain Grho := hdomGrho ▸ hv
    have huD : u ∈ Erho.domain := by
      apply mem_domain_of_energy_eq u
      rw [hrhoform u]
      exact huG
    have hvD : v ∈ Erho.domain := by
      apply mem_domain_of_energy_eq v
      rw [hrhoform v]
      exact hvG
    have huvD : u + v ∈ Erho.domain := Erho.domain.add_mem huD hvD
    have huvG : u + v ∈ limitFormDomain GE := hGE_add u v hu hv
    have humvD : u - v ∈ Erho.domain := Erho.domain.sub_mem huD hvD
    have humvG : u - v ∈ limitFormDomain GE := hGE_sub u v hu hv
    have hformpolar : Erho.form u v =
        (Erho.form (u + v) (u + v) - Erho.form (u - v) (u - v)) / 4 := by
      have hplus : Erho.form (u + v) (u + v) =
          Erho.form u u + 2 * Erho.form u v + Erho.form v v := by
        calc
          Erho.form (u + v) (u + v) =
              Erho.form u (u + v) + Erho.form v (u + v) :=
            Erho.form_add_left u huD v hvD (u + v) huvD
          _ = Erho.form (u + v) u + Erho.form (u + v) v := by
            rw [Erho.form_symm u huD (u + v) huvD,
              Erho.form_symm v hvD (u + v) huvD]
          _ = (Erho.form u u + Erho.form v u) +
              (Erho.form u v + Erho.form v v) := by
            rw [Erho.form_add_left u huD v hvD u huD,
              Erho.form_add_left u huD v hvD v hvD]
          _ = Erho.form u u + 2 * Erho.form u v + Erho.form v v := by
            rw [Erho.form_symm v hvD u huD]
            ring
      have hminus : Erho.form (u - v) (u - v) =
          Erho.form u u - 2 * Erho.form u v + Erho.form v v := by
        have hneg : (-v : DomainL2 Q) ∈ Erho.domain := Erho.domain.neg_mem hvD
        have hsumneg : u + (-v : DomainL2 Q) ∈ Erho.domain := Erho.domain.add_mem huD hneg
        have hneg_u : Erho.form (-v) u = -Erho.form v u := by
          simpa using (Erho.form_smul_left (-1) v hvD u huD)
        have hv_neg : Erho.form v (-v) = -Erho.form v v := by
          calc
            Erho.form v (-v) = Erho.form (-v) v := Erho.form_symm v hvD (-v) hneg
            _ = -Erho.form v v := by
              simpa using (Erho.form_smul_left (-1) v hvD v hvD)
        have hu_neg : Erho.form u (-v) = -Erho.form u v := by
          calc
            Erho.form u (-v) = Erho.form (-v) u := Erho.form_symm u huD (-v) hneg
            _ = -Erho.form v u := hneg_u
            _ = -Erho.form u v := by rw [Erho.form_symm v hvD u huD]
        have hneg_neg : Erho.form (-v) (-v) = Erho.form v v := by
          calc
            Erho.form (-v) (-v) = -Erho.form v (-v) := by
              simpa using (Erho.form_smul_left (-1) v hvD (-v) hneg)
            _ = Erho.form v v := by rw [hv_neg]; ring
        calc
          Erho.form (u - v) (u - v) =
              Erho.form (u + (-v)) (u + (-v)) := by rw [sub_eq_add_neg]
          _ = Erho.form u (u + (-v)) + Erho.form (-v) (u + (-v)) :=
            Erho.form_add_left u huD (-v) hneg (u + (-v)) hsumneg
          _ = Erho.form (u + (-v)) u + Erho.form (u + (-v)) (-v) := by
            rw [Erho.form_symm u huD (u + (-v)) hsumneg,
              Erho.form_symm (-v) hneg (u + (-v)) hsumneg]
          _ = (Erho.form u u + Erho.form (-v) u) +
              (Erho.form u (-v) + Erho.form (-v) (-v)) := by
            rw [Erho.form_add_left u huD (-v) hneg u huD,
              Erho.form_add_left u huD (-v) hneg (-v) hneg]
          _ = Erho.form u u - 2 * Erho.form u v + Erho.form v v := by
            rw [hneg_u, hu_neg, hneg_neg, Erho.form_symm v hvD u huD]
            ring
      rw [hplus, hminus]
      ring
    have hQcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
      rw [hQcube]
      exact (centeredCube_isBounded z0 hR).isCompact_closure
    have huE : u ∈ E.domain := mem_E_domain_of_energy_eq u (by
      rw [hEform u]
      exact hu)
    have hvE : v ∈ E.domain := mem_E_domain_of_energy_eq v (by
      rw [hEform v]
      exact hv)
    have huvE : u + v ∈ E.domain := E.domain.add_mem huE hvE
    have humvE : u - v ∈ E.domain := E.domain.sub_mem huE hvE
    let : IsFiniteMeasure (GammaE.measure (u + v)) :=
      ⟨GammaE.measure_univ_lt_top (u + v) huvE⟩
    let : IsFiniteMeasure (GammaE.measure (u - v)) :=
      ⟨GammaE.measure_univ_lt_top (u - v) humvE⟩
    have hcrossplus : GammaE.cross (u + v) (u + v) =
        (GammaE.measure (u + v)).toSignedMeasure := by
      ext B hB
      rw [GammaE.cross_self (u + v) huvE B hB,
        Measure.toSignedMeasure_apply_measurable hB]
      rfl
    have hcrossminus : GammaE.cross (u - v) (u - v) =
        (GammaE.measure (u - v)).toSignedMeasure := by
      ext B hB
      rw [GammaE.cross_self (u - v) humvE B hB,
        Measure.toSignedMeasure_apply_measurable hB]
      rfl
    have hplusInt : Integrable rho
        ((GammaE.measure (u + v)).restrict (Q : Set (SpatialCoordinates d))) := by
      exact (hrhocont.integrableOn_compact (μ := GammaE.measure (u + v)) hQcompact).integrable.mono_measure
        (Measure.restrict_mono_set _ subset_closure)
    have hminusInt : Integrable rho
        ((GammaE.measure (u - v)).restrict (Q : Set (SpatialCoordinates d))) := by
      exact (hrhocont.integrableOn_compact (μ := GammaE.measure (u - v)) hQcompact).integrable.mono_measure
        (Measure.restrict_mono_set _ subset_closure)
    have hcrosspolar : GammaE.cross u v =
        (1 / 4 : ℝ) •
          (GammaE.cross (u + v) (u + v) - GammaE.cross (u - v) (u - v)) := by
      ext B hB
      rw [GammaE.cross_eq_polarization huE hvE B]
      simp [sub_apply, smul_eq_mul]
      ring
    have hcrossint : _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho =
        (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u + v)) -
          ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u - v))) / 4 := by
      rw [hcrosspolar,
        aux_prop_21_signedIntegralOn_nonneg_smul _ _ (by norm_num)]
      rw [hcrossplus, hcrossminus]
      rw [aux_prop_21_signedIntegralOn_toSignedMeasure_sub
        (GammaE.measure (u + v)) (GammaE.measure (u - v))
        (Q : Set (SpatialCoordinates d)) (Q.isOpen.measurableSet) rho hplusInt hminusInt]
      ring
    calc
      Erho.form u v =
          (Erho.form (u + v) (u + v) - Erho.form (u - v) (u - v)) / 4 := hformpolar
      _ =
          (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u + v)) -
            ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u - v))) / 4 := by
        rw [hdiag (u + v) huvG, hdiag (u - v) humvG]
      _ = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross u v)
          (Q : Set (SpatialCoordinates d)) rho := hcrossint.symm
  refine ⟨hdomGrho, hmosco.1, hmosco.2, hGrhoEnergy, hbilinear⟩

end SubdiffusiveProcess.Paper
