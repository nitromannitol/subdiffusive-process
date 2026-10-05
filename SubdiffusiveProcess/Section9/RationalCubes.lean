module

public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet

@[expose] public section

open SubdiffusiveProcess TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- The countable family of rational-centred cubes with integer triadic side. -/
abbrev RationalCubeIndex (d : ℕ) := (Fin d → ℚ) × ℤ

def rationalCubeCenter (d : ℕ) (n : RationalCubeIndex d) : SpatialCoordinates d :=
  fun i => (n.1 i : ℝ)

def rationalCubeSide (d : ℕ) (n : RationalCubeIndex d) : ℝ := (3 : ℝ) ^ n.2

theorem rationalCubeSide_pos (d : ℕ) (n : RationalCubeIndex d) :
    0 < rationalCubeSide d n := zpow_pos (by norm_num) n.2

def rationalCube (d : ℕ) (n : RationalCubeIndex d) : Opens (SpatialCoordinates d) :=
  centeredCube (rationalCubeCenter d n) (rationalCubeSide d n) (rationalCubeSide_pos d n)

end SubdiffusiveProcess.Section9
