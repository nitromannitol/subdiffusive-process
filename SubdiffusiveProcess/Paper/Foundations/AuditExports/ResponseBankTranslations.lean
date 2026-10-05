module

public import SubdiffusiveProcess.Paper.prop_as_response_bank
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The shifted zero-infrared coefficient is the physical spatial translate
of the same cutoff coefficient, at every point and cutoff. -/
theorem cutoff_coefficient_zero_infrared_shift {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (w : SpatialCoordinates d) (omega : BilateralField d)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      (aux_responseBankShift w omega) N x =
    cutoffCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      omega N (cubeDilation w 0 1 x) := by
  rfl

/-- S15: the full response bank on every positive triadic cube, with each
relative-tail envelope uniform over all deterministic environment shifts.
For the zero-infrared branch these are the paper's translated coefficient and
translated data. The same limit is used in convergence and every tail event.
All supplier inputs are constructed inside the proof. -/
theorem response_bank_fixed_cube_translations_of_infrared
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ model : _root_.SubdiffusiveProcess.Model.GMCModel d,
        model.delta ≤ min 1 delta0 →
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (_HI : InfraredCharacterization model H),
      ∀ (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ)
        (hr : ∀ i : I, 0 < r i)
        (_htriadic : ∀ i : I, ∃ j : ℤ, r i = (3 : ℝ) ^ j),
      ∀ (phi : I → SpatialCoordinates d → ℝ)
        (hphi : ∀ i : I, ContDiff ℝ ∞ (phi i)),
      ∀ (fD fN : ∀ i : I, DomainL2 (centeredCube (z i) (r i) (hr i)))
        (KD KN : I → ℝ),
        (∀ i : I, 0 ≤ KD i) →
        (∀ i : I, 0 ≤ KN i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i) →
        (∀ i : I, (∫ x in (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d)),
          (fN i : SpatialCoordinates d → ℝ) x) = 0) →
      ∀ (p : I → (Fin d → ℝ)),
      let hP : ∀ i : I, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖ :=
        fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).1
      let hP0 : ∀ i : I, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖ :=
        fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).2
      let b : ∀ i : I, weakSobolevGraph
          (centeredCube (z i) (r i) (hr i)) :=
        fun i => Classical.choose
          (aux_source_response_bank_smooth_weak_witness
            (z i) (r i) (hr i) (phi i) (hphi i))
      let SD : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => killedResponseSpace (hP i)
      let SN : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => meanZeroResponseSpace (hP0 i)
      let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun i infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
            cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
          match branch.val with
          | 0 => dirichletResponse (SD i) (a) (b i)
          | 1 => inverseResponse (SD i) (a)
              ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
          | 2 => inverseResponse (SN i) (a)
              ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
          | _ => affineInverseNeumannResponse (hP0 i) (a) (p i)
      let Shift : SpatialCoordinates d → BilateralField d → BilateralField d :=
        fun w omega => fun j : ℤ =>
          (omega j).comp
            (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Rlim : I → Bool → Fin 4 → BilateralField d → ℝ,
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Measurable (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          ∀ omega : BilateralField d, 0 ≤ Rlim i infrared branch omega) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          TendstoInMeasure P (Rsp i infrared branch) atTop
            (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch omega +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N omega -
                        Rlim i infrared branch omega|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
        (∀ᵐ omega ∂P, ∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Tendsto (fun N : ℕ => Rsp i infrared branch N omega) atTop
            (nhds (Rlim i infrared branch omega))) ∧
        (∀ i : I, ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ w : SpatialCoordinates d, ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch (Shift w omega) +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N (Shift w omega) -
                        Rlim i infrared branch (Shift w omega)|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) := by
  classical
  let Jc : in_J d := Classical.choice (inputs_J_witness d hd)
  let Pc : in_poincare d hd Jc := Classical.choice (inputs_poincare_witness d hd Jc)
  let Xc : in_extension d hd Jc := Classical.choice (inputs_extension_witness d hd Jc)
  let Sf : SobolevFoundationalInput d hd := Classical.choice (inputs_Sf_witness d hd)
  let W : SmallPerturbationInput d := Classical.choice (inputs_W_witness d)
  let Cp : CampanatoInput d := Classical.choice (inputs_Cp_witness d)
  obtain ⟨Cresp, B, delta0, Cgeom, hCresp, hBnonempty, hB128,
    hBord, hdelta0, hdelta1, hCgeom, hmain⟩ :=
    prop_as_response_bank d hd Jc Pc Xc Sf W Cp
      (inputs_deterministic_witness d hd) inputs_hES_witness
      (inputs_step_witness d hd) (inputs_baseline_witness d hd)
      (inputs_Interp_witness d hd)
  refine ⟨delta0, Cgeom, hdelta0, hCgeom, ?_⟩
  intro model hdelta H HI I _ z r hr htriadic phi hphi
    fD fN KD KN hKD hKN hfD hfN hfNmean p hP hP0 b SD SN Rsp Shift P
  obtain ⟨_, hrest⟩ := hmain model (inputs_regularity_witness d model)
    (inputs_iteration_witness d hd model Jc) hdelta
  obtain ⟨L, hLm, hLn, hLt, htail, hae, _⟩ :=
    hrest H HI I z r hr htriadic phi hphi fD fN KD KN hKD hKN hfD hfN hfNmean p
  refine ⟨L, hLm, hLn, hLt, htail, hae, ?_⟩
  have hZ : ∀ i infrared branch N, Measurable (Rsp i infrared branch N) :=
    aux_actual_response_bank_rsp_measurable model H HI z r hr hP hP0 b fD fN p
  intro i eps heps
  obtain ⟨Ce, ce, Ne, hCe, hce, hN⟩ := htail i eps heps
  refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
  intro w N hNe infrared branch
  exact (aux_response_bank_stationary_tail_transfer d model Rsp L hZ hLm
    (Cgeom * eps) (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) i N infrared branch w).trans_le
      (hN N hNe infrared branch)

/-- S15 for the actual coefficients: the characterized infrared field is
produced internally. The bank, full-sequence limits and fixed-cube translation
bounds share that field and the same limits. -/
theorem response_bank_fixed_cube_translations
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ model : _root_.SubdiffusiveProcess.Model.GMCModel d,
        model.delta ≤ min 1 delta0 →
        ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (_HI : InfraredCharacterization model H),
      ∀ (I : Type) [Countable I]
        (z : I → SpatialCoordinates d) (r : I → ℝ)
        (hr : ∀ i : I, 0 < r i)
        (_htriadic : ∀ i : I, ∃ j : ℤ, r i = (3 : ℝ) ^ j),
      ∀ (phi : I → SpatialCoordinates d → ℝ)
        (hphi : ∀ i : I, ContDiff ℝ ∞ (phi i)),
      ∀ (fD fN : ∀ i : I, DomainL2 (centeredCube (z i) (r i) (hr i)))
        (KD KN : I → ℝ),
        (∀ i : I, 0 ≤ KD i) →
        (∀ i : I, 0 ≤ KN i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fD i : SpatialCoordinates d → ℝ) x| ≤ KD i) →
        (∀ i : I, ∀ᵐ x ∂volume.restrict
          (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          |(fN i : SpatialCoordinates d → ℝ) x| ≤ KN i) →
        (∀ i : I, (∫ x in (centeredCube (z i) (r i) (hr i) :
          Set (SpatialCoordinates d)),
          (fN i : SpatialCoordinates d → ℝ) x) = 0) →
      ∀ (p : I → (Fin d → ℝ)),
      let hP : ∀ i : I, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖ :=
        fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).1
      let hP0 : ∀ i : I, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
          (centeredCube (z i) (r i) (hr i)),
        ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph
            (centeredCube (z i) (r i) (hr i))) u‖ :=
        fun i => (aux_source_response_bank_cube_poincare hd (z i) (r i) (hr i)).2
      let b : ∀ i : I, weakSobolevGraph
          (centeredCube (z i) (r i) (hr i)) :=
        fun i => Classical.choose
          (aux_source_response_bank_smooth_weak_witness
            (z i) (r i) (hr i) (phi i) (hphi i))
      let SD : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => killedResponseSpace (hP i)
      let SN : ∀ i : I, ResponseSpace (centeredCube (z i) (r i) (hr i)) :=
        fun i => meanZeroResponseSpace (hP0 i)
      let Rsp : I → Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun i infrared branch N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
            cutoffPositiveCoefficient model Hused omega N (z i) (hr i)
          match branch.val with
          | 0 => dirichletResponse (SD i) (a) (b i)
          | 1 => inverseResponse (SD i) (a)
              ((sobolevVolumeLoad (fD i)).comp (SD i).space.subtypeL)
          | 2 => inverseResponse (SN i) (a)
              ((sobolevVolumeLoad (fN i)).comp (SN i).space.subtypeL)
          | _ => affineInverseNeumannResponse (hP0 i) (a) (p i)
      let Shift : SpatialCoordinates d → BilateralField d → BilateralField d :=
        fun w omega => fun j : ℤ =>
          (omega j).comp
            (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
              C(SpatialCoordinates d, SpatialCoordinates d))
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Rlim : I → Bool → Fin 4 → BilateralField d → ℝ,
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Measurable (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          ∀ omega : BilateralField d, 0 ≤ Rlim i infrared branch omega) ∧
        (∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          TendstoInMeasure P (Rsp i infrared branch) atTop
            (Rlim i infrared branch)) ∧
        (∀ i : I, ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch omega +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N omega -
                        Rlim i infrared branch omega|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) ∧
        (∀ᵐ omega ∂P, ∀ i : I, ∀ infrared : Bool, ∀ branch : Fin 4,
          Tendsto (fun N : ℕ => Rsp i infrared branch N omega) atTop
            (nhds (Rlim i infrared branch omega))) ∧
        (∀ i : I, ∀ eps : ℝ, 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ,
            0 < Ce ∧ 0 < ce ∧
            ∀ w : SpatialCoordinates d, ∀ N : ℕ, Ne ≤ N →
              ∀ infrared : Bool, ∀ branch : Fin 4,
                P {omega |
                    Cgeom * eps * Rlim i infrared branch (Shift w omega) +
                        Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |Rsp i infrared branch N (Shift w omega) -
                        Rlim i infrared branch (Shift w omega)|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, h⟩ :=
    response_bank_fixed_cube_translations_of_infrared d hd
  refine ⟨delta0, Cgeom, hdelta0, hCgeom, ?_⟩
  intro model hdelta
  obtain ⟨H, HI⟩ := SubdiffusiveProcess.exists_infraredCharacterization hd model
  exact ⟨H, HI, h model hdelta H HI⟩

end SubdiffusiveProcess.AuditExports
