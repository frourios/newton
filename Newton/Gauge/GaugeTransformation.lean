import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Newton.Gauge.LieAlgebra

open Matrix

namespace Newton

variable {N : ℕ}

/-- Element of SU(N) group
N×N complex matrix g satisfying:
1. Unitary: g g† = 1
2. Determinant one: det(g) = 1
-/
structure SUNGroup (N : ℕ) where
  /-- Matrix representation -/
  matrix : Matrix (Fin N) (Fin N) ℂ
  /-- Unitary condition: g g† = 1 -/
  unitary : matrix * conjTranspose matrix = 1
  /-- Special condition: det(g) = 1 -/
  det_one : det matrix = 1

namespace SUNGroup

/-- SUNGroup equality is matrix equality -/
theorem ext {g h : SUNGroup N} (hm : g.matrix = h.matrix) : g = h := by
  cases g; cases h; simp_all

/-- Alternative form of unitary condition: g† g = 1 -/
theorem unitary' (g : SUNGroup N) :
    conjTranspose g.matrix * g.matrix = 1 := by
  -- For unitary matrices, g g† = 1 ⟺ g† g = 1
  -- Since det g = 1 ≠ 0, g is invertible
  have h_isUnit : IsUnit (det g.matrix) := by
    rw [g.det_one]; exact isUnit_one
  have h_inv : g.matrix⁻¹ = conjTranspose g.matrix := by
    -- From g g† = 1, we get g⁻¹ = g†
    exact inv_eq_right_inv g.unitary
  -- g† g = g⁻¹ g = 1
  rw [← h_inv]
  exact nonsing_inv_mul g.matrix h_isUnit

/-- Identity element -/
instance : One (SUNGroup N) where
  one := {
    matrix := 1
    unitary := by simp [conjTranspose_one]
    det_one := by simp
  }

/-- Multiplication -/
instance : Mul (SUNGroup N) where
  mul g h := {
    matrix := g.matrix * h.matrix
    unitary := by
      rw [conjTranspose_mul]
      calc (g.matrix * h.matrix) * (conjTranspose h.matrix * conjTranspose g.matrix)
          = g.matrix * (h.matrix * conjTranspose h.matrix) * conjTranspose g.matrix := by
            noncomm_ring
        _ = g.matrix * 1 * conjTranspose g.matrix := by rw [h.unitary]
        _ = g.matrix * conjTranspose g.matrix := by rw [mul_one]
        _ = 1 := g.unitary
    det_one := by
      rw [det_mul, g.det_one, h.det_one, one_mul]
  }

/-- Inverse element -/
noncomputable instance : Inv (SUNGroup N) where
  inv g := {
    matrix := conjTranspose g.matrix
    unitary := by
      rw [conjTranspose_conjTranspose]
      exact g.unitary'
    det_one := by
      rw [det_conjTranspose]
      simp only [g.det_one, star_one]
  }

/-- Matrix of identity element -/
@[simp]
theorem one_matrix : (1 : SUNGroup N).matrix = 1 := rfl

/-- Matrix of multiplication -/
@[simp]
theorem mul_matrix (g h : SUNGroup N) : (g * h).matrix = g.matrix * h.matrix := rfl

/-- Matrix of inverse element -/
@[simp]
theorem inv_matrix (g : SUNGroup N) : g⁻¹.matrix = conjTranspose g.matrix := rfl

/-- Right identity law -/
@[simp]
theorem mul_one (g : SUNGroup N) : g * 1 = g := by
  apply ext
  simp

/-- Left identity law -/
@[simp]
theorem one_mul (g : SUNGroup N) : 1 * g = g := by
  apply ext
  simp

/-- Right inverse law -/
@[simp]
theorem mul_inv (g : SUNGroup N) : g * g⁻¹ = 1 := by
  apply ext
  simp only [mul_matrix, inv_matrix, one_matrix]
  exact g.unitary

/-- Left inverse law -/
@[simp]
theorem inv_mul (g : SUNGroup N) : g⁻¹ * g = 1 := by
  apply ext
  simp only [mul_matrix, inv_matrix, one_matrix]
  exact g.unitary'

/-- Associativity of multiplication -/
theorem mul_assoc (g h k : SUNGroup N) : g * h * k = g * (h * k) := by
  apply ext
  simp only [mul_matrix]
  exact Matrix.mul_assoc _ _ _

end SUNGroup

/-- Adjoint action: g A g⁻¹ = g A g†
Adjoint action of SU(N) element g on su(N) element A.
The result is again an element of su(N).
-/
noncomputable def adjointAction (g : SUNGroup N) (A : SuNAlgebra N) : SuNAlgebra N where
  matrix := g.matrix * A.matrix * conjTranspose g.matrix
  trace_zero := by
    -- Tr(gAg†) = Tr(g†gA) = Tr(A) = 0 (cyclicity of trace)
    have h1 : trace (g.matrix * A.matrix * conjTranspose g.matrix) =
        trace (conjTranspose g.matrix * g.matrix * A.matrix) := by
      rw [trace_mul_cycle, Matrix.mul_assoc]
    rw [h1, g.unitary', one_mul]
    exact A.trace_zero
  anti_hermitian := by
    -- (gAg†)† = (g†)† A† g† = g (-A) g† = -gAg†
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [A.anti_hermitian]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    rw [Matrix.mul_assoc]

namespace adjointAction

/-- Adjoint action by identity is the identity map -/
@[simp]
theorem one_action (A : SuNAlgebra N) : adjointAction (1 : SUNGroup N) A = A := by
  apply SuNAlgebra.ext
  simp [adjointAction, conjTranspose_one]

/-- Composition rule for adjoint action: Ad(gh)(A) = Ad(g)(Ad(h)(A)) -/
theorem compose (g h : SUNGroup N) (A : SuNAlgebra N) :
    adjointAction (g * h) A = adjointAction g (adjointAction h A) := by
  apply SuNAlgebra.ext
  simp only [adjointAction, SUNGroup.mul_matrix, conjTranspose_mul]
  -- (gh) A (gh)† = (gh) A (h† g†) = g (h A h†) g†
  noncomm_ring

/-- Adjoint action preserves addition -/
theorem add (g : SUNGroup N) (A B : SuNAlgebra N) :
    adjointAction g (A + B) = adjointAction g A + adjointAction g B := by
  apply SuNAlgebra.ext
  simp only [adjointAction, SuNAlgebra.add_matrix]
  rw [Matrix.mul_add, Matrix.add_mul]

/-- Adjoint action preserves zero -/
@[simp]
theorem zero (g : SUNGroup N) : adjointAction g (0 : SuNAlgebra N) = 0 := by
  apply SuNAlgebra.ext
  simp [adjointAction]

/-- Adjoint action preserves Lie bracket -/
theorem bracket (g : SUNGroup N) (A B : SuNAlgebra N) :
    adjointAction g ⁅A, B⁆ = ⁅adjointAction g A, adjointAction g B⁆ := by
  apply SuNAlgebra.ext
  simp only [adjointAction, SuNAlgebra.lie_def]
  -- g [A, B] g† = g (AB - BA) g† = gAg† gBg† - gBg† gAg† = [gAg†, gBg†]
  -- Using g† g = 1
  have h := g.unitary'
  -- LHS: g(AB - BA)g† = gABg† - gBAg†
  -- RHS: (gAg†)(gBg†) - (gBg†)(gAg†)
  -- Since g†g = 1, we have gABg† = gA(g†g)Bg† = (gAg†)(gBg†)
  let gm := g.matrix
  let gh := conjTranspose g.matrix
  let am := A.matrix
  let bm := B.matrix
  have eq1 : gm * am * bm * gh = gm * am * gh * (gm * bm * gh) := by
    calc gm * am * bm * gh
        = gm * am * (gh * gm) * bm * gh := by rw [h]; simp only [mul_one]
      _ = gm * am * gh * (gm * bm * gh) := by noncomm_ring
  have eq2 : gm * bm * am * gh = gm * bm * gh * (gm * am * gh) := by
    calc gm * bm * am * gh
        = gm * bm * (gh * gm) * am * gh := by rw [h]; simp only [mul_one]
      _ = gm * bm * gh * (gm * am * gh) := by noncomm_ring
  calc gm * (am * bm - bm * am) * gh
      = gm * am * bm * gh - gm * bm * am * gh := by noncomm_ring
    _ = gm * am * gh * (gm * bm * gh) - gm * bm * gh * (gm * am * gh) := by rw [eq1, eq2]

end adjointAction

end Newton
