import Newton.Gauge.LieAlgebra

open Matrix

namespace Newton

/-- Pauli matrix σ₁ (X matrix) -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![1, 0]]

/-- Pauli matrix σ₂ (Y matrix) -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, -Complex.I], ![Complex.I, 0]]

/-- Pauli matrix σ₃ (Z matrix) -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![1, 0], ![0, -1]]

@[simp]
theorem pauliX_trace : trace pauliX = 0 := by
  simp only [pauliX, trace, Fin.sum_univ_two, diag, cons_val_zero, cons_val_one]
  ring

@[simp]
theorem pauliY_trace : trace pauliY = 0 := by
  simp only [pauliY, trace, Fin.sum_univ_two, diag, cons_val_zero, cons_val_one]
  ring

@[simp]
theorem pauliZ_trace : trace pauliZ = 0 := by
  simp only [pauliZ, trace, Fin.sum_univ_two, diag, cons_val_zero, cons_val_one]
  ring

/-- Pauli matrix σ₁ is Hermitian -/
theorem pauliX_hermitian : conjTranspose pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliX, conjTranspose, transpose_apply, map_apply]
  all_goals simp

/-- Pauli matrix σ₃ is Hermitian -/
theorem pauliZ_hermitian : conjTranspose pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliZ, conjTranspose, transpose_apply, map_apply]
  all_goals simp

/-- Pauli matrix σ₂ is Hermitian -/
theorem pauliY_hermitian : conjTranspose pauliY = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliY, conjTranspose, transpose_apply, map_apply]
  · simp
  · simp [Complex.star_def, Complex.conj_I]
  · simp [Complex.star_def, Complex.conj_I]
  · simp

/-- Matrix representation of su(2) generator T₁ = -i σ₁ / 2 -/
noncomputable def su2Gen1Matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2 : ℂ) • pauliX

/-- Matrix representation of su(2) generator T₂ = -i σ₂ / 2 -/
noncomputable def su2Gen2Matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2 : ℂ) • pauliY

/-- Matrix representation of su(2) generator T₃ = -i σ₃ / 2 -/
noncomputable def su2Gen3Matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2 : ℂ) • pauliZ

/-- Trace of su(2) generator T₁ is zero -/
@[simp]
theorem su2Gen1Matrix_trace : trace su2Gen1Matrix = 0 := by
  simp only [su2Gen1Matrix, trace_smul, pauliX_trace, smul_zero]

/-- Trace of su(2) generator T₂ is zero -/
@[simp]
theorem su2Gen2Matrix_trace : trace su2Gen2Matrix = 0 := by
  simp only [su2Gen2Matrix, trace_smul, pauliY_trace, smul_zero]

/-- Trace of su(2) generator T₃ is zero -/
@[simp]
theorem su2Gen3Matrix_trace : trace su2Gen3Matrix = 0 := by
  simp only [su2Gen3Matrix, trace_smul, pauliZ_trace, smul_zero]

/-- Auxiliary lemma: star(-I/2) = -(-I/2) -/
private theorem star_neg_I_div_2 : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
  simp only [star_div₀, star_neg, Complex.star_def, Complex.conj_I, h2]
  ring

/-- su(2) generator T₁ is anti-Hermitian -/
theorem su2Gen1Matrix_antiHermitian : conjTranspose su2Gen1Matrix = -su2Gen1Matrix := by
  unfold su2Gen1Matrix
  simp only [conjTranspose_smul, pauliX_hermitian, neg_smul, star_neg_I_div_2]

/-- su(2) generator T₂ is anti-Hermitian -/
theorem su2Gen2Matrix_antiHermitian : conjTranspose su2Gen2Matrix = -su2Gen2Matrix := by
  unfold su2Gen2Matrix
  simp only [conjTranspose_smul, pauliY_hermitian, neg_smul, star_neg_I_div_2]

/-- su(2) generator T₃ is anti-Hermitian -/
theorem su2Gen3Matrix_antiHermitian : conjTranspose su2Gen3Matrix = -su2Gen3Matrix := by
  unfold su2Gen3Matrix
  simp only [conjTranspose_smul, pauliZ_hermitian, neg_smul, star_neg_I_div_2]

/-- Construct su(2) generator T₁ as SuNAlgebra -/
noncomputable def su2Gen1 : SuNAlgebra 2 where
  matrix := su2Gen1Matrix
  trace_zero := su2Gen1Matrix_trace
  anti_hermitian := su2Gen1Matrix_antiHermitian

/-- Construct su(2) generator T₂ as SuNAlgebra -/
noncomputable def su2Gen2 : SuNAlgebra 2 where
  matrix := su2Gen2Matrix
  trace_zero := su2Gen2Matrix_trace
  anti_hermitian := su2Gen2Matrix_antiHermitian

/-- Construct su(2) generator T₃ as SuNAlgebra -/
noncomputable def su2Gen3 : SuNAlgebra 2 where
  matrix := su2Gen3Matrix
  trace_zero := su2Gen3Matrix_trace
  anti_hermitian := su2Gen3Matrix_antiHermitian

/-- (0,0) component of the matrix product (pauliX * pauliY) -/
private theorem pauliX_mul_pauliY_00 : (pauliX * pauliY) 0 0 = Complex.I := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (0,1) component of the matrix product (pauliX * pauliY) -/
private theorem pauliX_mul_pauliY_01 : (pauliX * pauliY) 0 1 = 0 := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (1,0) component of the matrix product (pauliX * pauliY) -/
private theorem pauliX_mul_pauliY_10 : (pauliX * pauliY) 1 0 = 0 := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (1,1) component of the matrix product (pauliX * pauliY) -/
private theorem pauliX_mul_pauliY_11 : (pauliX * pauliY) 1 1 = -Complex.I := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (0,0) component of the matrix product (pauliY * pauliX) -/
private theorem pauliY_mul_pauliX_00 : (pauliY * pauliX) 0 0 = -Complex.I := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (0,1) component of the matrix product (pauliY * pauliX) -/
private theorem pauliY_mul_pauliX_01 : (pauliY * pauliX) 0 1 = 0 := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (1,0) component of the matrix product (pauliY * pauliX) -/
private theorem pauliY_mul_pauliX_10 : (pauliY * pauliX) 1 0 = 0 := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- (1,1) component of the matrix product (pauliY * pauliX) -/
private theorem pauliY_mul_pauliX_11 : (pauliY * pauliX) 1 1 = Complex.I := by
  simp only [mul_apply, pauliX, pauliY, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]
  ring

/-- Any element of Fin 2 is either 0 or 1 -/
private theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- (0,0) component of [σ₁, σ₂] -/
private theorem pauliXY_comm_00 :
    (pauliX * pauliY - pauliY * pauliX) 0 0 = ((2 * Complex.I) • pauliZ) 0 0 := by
  simp only [sub_apply, smul_apply, pauliZ, smul_eq_mul,
             cons_val_zero, pauliX_mul_pauliY_00, pauliY_mul_pauliX_00]
  ring

/-- (0,1) component of [σ₁, σ₂] -/
private theorem pauliXY_comm_01 :
    (pauliX * pauliY - pauliY * pauliX) 0 1 = ((2 * Complex.I) • pauliZ) 0 1 := by
  simp only [sub_apply, smul_apply, pauliZ, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliX_mul_pauliY_01, pauliY_mul_pauliX_01]
  ring

/-- (1,0) component of [σ₁, σ₂] -/
private theorem pauliXY_comm_10 :
    (pauliX * pauliY - pauliY * pauliX) 1 0 = ((2 * Complex.I) • pauliZ) 1 0 := by
  simp only [sub_apply, smul_apply, pauliZ, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliX_mul_pauliY_10, pauliY_mul_pauliX_10]
  ring

/-- (1,1) component of [σ₁, σ₂] -/
private theorem pauliXY_comm_11 :
    (pauliX * pauliY - pauliY * pauliX) 1 1 = ((2 * Complex.I) • pauliZ) 1 1 := by
  simp only [sub_apply, smul_apply, pauliZ, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliX_mul_pauliY_11, pauliY_mul_pauliX_11]
  ring

/-- [σ₁, σ₂] = 2i σ₃ -/
private theorem pauliX_pauliY_commutator :
    pauliX * pauliY - pauliY * pauliX = (2 * Complex.I) • pauliZ := by
  ext i j
  rcases fin2_eq_zero_or_one i with hi | hi <;>
  rcases fin2_eq_zero_or_one j with hj | hj <;>
  simp only [hi, hj, pauliXY_comm_00, pauliXY_comm_01, pauliXY_comm_10, pauliXY_comm_11]

/-- [T₁, T₂] = T₃

Calculation: [T₁, T₂] = [-iσ₁/2, -iσ₂/2] = (-i/2)² [σ₁, σ₂] = (-1/4)(2i σ₃) = (-i/2) σ₃ = T₃
-/
theorem su2_bracket_12 : ⁅su2Gen1, su2Gen2⁆ = su2Gen3 := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, su2Gen1, su2Gen2, su2Gen3,
             su2Gen1Matrix, su2Gen2Matrix, su2Gen3Matrix]
  -- (-I/2) • σ₁ * (-I/2) • σ₂ - (-I/2) • σ₂ * (-I/2) • σ₁
  -- = (-I/2)² (σ₁ σ₂ - σ₂ σ₁) = (-1/4) [σ₁, σ₂]
  have h1 : (-Complex.I / 2 : ℂ) • pauliX * ((-Complex.I / 2 : ℂ) • pauliY) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliX * pauliY) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (-Complex.I / 2 : ℂ) • pauliY * ((-Complex.I / 2 : ℂ) • pauliX) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliY * pauliX) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h2, ← smul_sub, pauliX_pauliY_commutator, smul_smul]
  -- Calculate coefficient: (-I/2)² * 2I = (-1/4) * 2I = -I/2
  have hcoef : (-Complex.I / 2) * (-Complex.I / 2) * (2 * Complex.I) = -Complex.I / 2 := by
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    ring_nf
    rw [hI3]
    ring
  rw [hcoef]

/-- Components of the matrix product (pauliY * pauliZ) -/
private theorem pauliY_mul_pauliZ_00 : (pauliY * pauliZ) 0 0 = 0 := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliY_mul_pauliZ_01 : (pauliY * pauliZ) 0 1 = Complex.I := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliY_mul_pauliZ_10 : (pauliY * pauliZ) 1 0 = Complex.I := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliY_mul_pauliZ_11 : (pauliY * pauliZ) 1 1 = 0 := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring

/-- Components of the matrix product (pauliZ * pauliY) -/
private theorem pauliZ_mul_pauliY_00 : (pauliZ * pauliY) 0 0 = 0 := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_01 : (pauliZ * pauliY) 0 1 = -Complex.I := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_10 : (pauliZ * pauliY) 1 0 = -Complex.I := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliY_11 : (pauliZ * pauliY) 1 1 = 0 := by
  simp only [mul_apply, pauliY, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring

/-- Components of [σ₂, σ₃] -/
private theorem pauliYZ_comm_00 :
    (pauliY * pauliZ - pauliZ * pauliY) 0 0 = ((2 * Complex.I) • pauliX) 0 0 := by
  simp only [sub_apply, smul_apply, pauliX, smul_eq_mul,
             cons_val_zero, pauliY_mul_pauliZ_00, pauliZ_mul_pauliY_00]; ring
private theorem pauliYZ_comm_01 :
    (pauliY * pauliZ - pauliZ * pauliY) 0 1 = ((2 * Complex.I) • pauliX) 0 1 := by
  simp only [sub_apply, smul_apply, pauliX, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliY_mul_pauliZ_01, pauliZ_mul_pauliY_01]; ring
private theorem pauliYZ_comm_10 :
    (pauliY * pauliZ - pauliZ * pauliY) 1 0 = ((2 * Complex.I) • pauliX) 1 0 := by
  simp only [sub_apply, smul_apply, pauliX, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliY_mul_pauliZ_10, pauliZ_mul_pauliY_10]; ring
private theorem pauliYZ_comm_11 :
    (pauliY * pauliZ - pauliZ * pauliY) 1 1 = ((2 * Complex.I) • pauliX) 1 1 := by
  simp only [sub_apply, smul_apply, pauliX, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliY_mul_pauliZ_11, pauliZ_mul_pauliY_11]; ring

/-- [σ₂, σ₃] = 2i σ₁ -/
private theorem pauliY_pauliZ_commutator :
    pauliY * pauliZ - pauliZ * pauliY = (2 * Complex.I) • pauliX := by
  ext i j
  rcases fin2_eq_zero_or_one i with hi | hi <;>
  rcases fin2_eq_zero_or_one j with hj | hj <;>
  simp only [hi, hj, pauliYZ_comm_00, pauliYZ_comm_01, pauliYZ_comm_10, pauliYZ_comm_11]

/-- [T₂, T₃] = T₁ -/
theorem su2_bracket_23 : ⁅su2Gen2, su2Gen3⁆ = su2Gen1 := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, su2Gen1, su2Gen2, su2Gen3,
             su2Gen1Matrix, su2Gen2Matrix, su2Gen3Matrix]
  have h1 : (-Complex.I / 2 : ℂ) • pauliY * ((-Complex.I / 2 : ℂ) • pauliZ) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliY * pauliZ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (-Complex.I / 2 : ℂ) • pauliZ * ((-Complex.I / 2 : ℂ) • pauliY) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliZ * pauliY) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h2, ← smul_sub, pauliY_pauliZ_commutator, smul_smul]
  have hcoef : (-Complex.I / 2) * (-Complex.I / 2) * (2 * Complex.I) = -Complex.I / 2 := by
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    ring_nf; rw [hI3]; ring
  rw [hcoef]

/-- Components of the matrix product (pauliZ * pauliX) -/
private theorem pauliZ_mul_pauliX_00 : (pauliZ * pauliX) 0 0 = 0 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliX_01 : (pauliZ * pauliX) 0 1 = 1 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliX_10 : (pauliZ * pauliX) 1 0 = -1 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliZ_mul_pauliX_11 : (pauliZ * pauliX) 1 1 = 0 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring

/-- Components of the matrix product (pauliX * pauliZ) -/
private theorem pauliX_mul_pauliZ_00 : (pauliX * pauliZ) 0 0 = 0 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliX_mul_pauliZ_01 : (pauliX * pauliZ) 0 1 = -1 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliX_mul_pauliZ_10 : (pauliX * pauliZ) 1 0 = 1 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring
private theorem pauliX_mul_pauliZ_11 : (pauliX * pauliZ) 1 1 = 0 := by
  simp only [mul_apply, pauliX, pauliZ, Fin.sum_univ_two, Fin.isValue,
             cons_val_zero, cons_val_one]; ring

/-- Components of [σ₃, σ₁] -/
private theorem pauliZX_comm_00 :
    (pauliZ * pauliX - pauliX * pauliZ) 0 0 = ((2 * Complex.I) • pauliY) 0 0 := by
  simp only [sub_apply, smul_apply, pauliY, smul_eq_mul,
             cons_val_zero, pauliZ_mul_pauliX_00, pauliX_mul_pauliZ_00]; ring
private theorem pauliZX_comm_01 :
    (pauliZ * pauliX - pauliX * pauliZ) 0 1 = ((2 * Complex.I) • pauliY) 0 1 := by
  simp only [sub_apply, smul_apply, pauliY, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliZ_mul_pauliX_01, pauliX_mul_pauliZ_01]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf; rw [hI2]; ring
private theorem pauliZX_comm_10 :
    (pauliZ * pauliX - pauliX * pauliZ) 1 0 = ((2 * Complex.I) • pauliY) 1 0 := by
  simp only [sub_apply, smul_apply, pauliY, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliZ_mul_pauliX_10, pauliX_mul_pauliZ_10]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf; rw [hI2]; ring
private theorem pauliZX_comm_11 :
    (pauliZ * pauliX - pauliX * pauliZ) 1 1 = ((2 * Complex.I) • pauliY) 1 1 := by
  simp only [sub_apply, smul_apply, pauliY, smul_eq_mul,
             cons_val_zero, cons_val_one,
             pauliZ_mul_pauliX_11, pauliX_mul_pauliZ_11]; ring

/-- [σ₃, σ₁] = 2i σ₂ -/
private theorem pauliZ_pauliX_commutator :
    pauliZ * pauliX - pauliX * pauliZ = (2 * Complex.I) • pauliY := by
  ext i j
  rcases fin2_eq_zero_or_one i with hi | hi <;>
  rcases fin2_eq_zero_or_one j with hj | hj <;>
  simp only [hi, hj, pauliZX_comm_00, pauliZX_comm_01, pauliZX_comm_10, pauliZX_comm_11]

/-- [T₃, T₁] = T₂ -/
theorem su2_bracket_31 : ⁅su2Gen3, su2Gen1⁆ = su2Gen2 := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, su2Gen1, su2Gen2, su2Gen3,
             su2Gen1Matrix, su2Gen2Matrix, su2Gen3Matrix]
  have h1 : (-Complex.I / 2 : ℂ) • pauliZ * ((-Complex.I / 2 : ℂ) • pauliX) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliZ * pauliX) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (-Complex.I / 2 : ℂ) • pauliX * ((-Complex.I / 2 : ℂ) • pauliZ) =
      ((-Complex.I / 2) * (-Complex.I / 2)) • (pauliX * pauliZ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h2, ← smul_sub, pauliZ_pauliX_commutator, smul_smul]
  have hcoef : (-Complex.I / 2) * (-Complex.I / 2) * (2 * Complex.I) = -Complex.I / 2 := by
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
    ring_nf; rw [hI3]; ring
  rw [hcoef]

/-- su(2) generator T₃ is nonzero -/
theorem su2Gen3_ne_zero : su2Gen3 ≠ 0 := by
  intro h
  have : su2Gen3.matrix = 0 := by rw [h]; rfl
  simp only [su2Gen3, su2Gen3Matrix] at this
  have h00 : ((-Complex.I / 2 : ℂ) • pauliZ) 0 0 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [this]
  simp only [smul_apply, pauliZ, cons_val_zero, smul_eq_mul, mul_one, zero_apply] at h00
  have : (-Complex.I / 2 : ℂ) = 0 := h00
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  simp only [neg_eq_zero, div_eq_zero_iff, hI, h2, or_self] at this

/-- Non-commutativity of su(2): [T₁, T₂] ≠ 0 -/
theorem su2_noncommutative : ⁅su2Gen1, su2Gen2⁆ ≠ 0 := by
  rw [su2_bracket_12]
  exact su2Gen3_ne_zero

/-- [T₂, T₁] = -T₃ (by antisymmetry) -/
theorem su2_bracket_21 : ⁅su2Gen2, su2Gen1⁆ = -su2Gen3 := by
  rw [← lie_skew, su2_bracket_12]

/-- [T₃, T₂] = -T₁ (by antisymmetry) -/
theorem su2_bracket_32 : ⁅su2Gen3, su2Gen2⁆ = -su2Gen1 := by
  rw [← lie_skew, su2_bracket_23]

/-- [T₁, T₃] = -T₂ (by antisymmetry) -/
theorem su2_bracket_13 : ⁅su2Gen1, su2Gen3⁆ = -su2Gen2 := by
  rw [← lie_skew, su2_bracket_31]

/-- su2Gen1 is nonzero -/
theorem su2Gen1_ne_zero : su2Gen1 ≠ 0 := by
  intro h
  have := su2_noncommutative
  rw [h] at this
  simp only [zero_lie, ne_eq, not_true_eq_false] at this

/-- su2Gen2 is nonzero -/
theorem su2Gen2_ne_zero : su2Gen2 ≠ 0 := by
  intro h
  have := su2_bracket_12
  rw [h] at this
  simp only [lie_zero] at this
  exact su2Gen3_ne_zero this.symm

/-- [T₂, [T₂, T₁]] = [T₂, -T₃] = -[T₂, T₃] = -T₁ -/
theorem su2_adjointSq_21 : ⁅su2Gen2, ⁅su2Gen2, su2Gen1⁆⁆ = -su2Gen1 := by
  rw [su2_bracket_21, lie_neg, su2_bracket_23]

/-- [T₃, [T₃, T₁]] = [T₃, T₂] = -T₁ -/
theorem su2_adjointSq_31 : ⁅su2Gen3, ⁅su2Gen3, su2Gen1⁆⁆ = -su2Gen1 := by
  rw [su2_bracket_31, su2_bracket_32]

/-- [T₁, [T₁, T₂]] = [T₁, T₃] = -T₂ -/
theorem su2_adjointSq_12 : ⁅su2Gen1, ⁅su2Gen1, su2Gen2⁆⁆ = -su2Gen2 := by
  rw [su2_bracket_12, su2_bracket_13]

/-- [T₃, [T₃, T₂]] = [T₃, T₁] = T₂ -/
theorem su2_adjointSq_32 : ⁅su2Gen3, ⁅su2Gen3, su2Gen2⁆⁆ = -su2Gen2 := by
  rw [su2_bracket_32, lie_neg, su2_bracket_31]

/-- [T₁, [T₁, T₃]] = [T₁, -T₂] = T₃ -/
theorem su2_adjointSq_13 : ⁅su2Gen1, ⁅su2Gen1, su2Gen3⁆⁆ = -su2Gen3 := by
  rw [su2_bracket_13, lie_neg, su2_bracket_12]

/-- [T₂, [T₂, T₃]] = [T₂, T₁] = -T₃ -/
theorem su2_adjointSq_23 : ⁅su2Gen2, ⁅su2Gen2, su2Gen3⁆⁆ = -su2Gen3 := by
  rw [su2_bracket_23, su2_bracket_21]

/-- Gell-Mann matrix λ₁ -/
def gellMann1 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]]

/-- Gell-Mann matrix λ₂ -/
def gellMann2 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, -Complex.I, 0], ![Complex.I, 0, 0], ![0, 0, 0]]

/-- Gell-Mann matrix λ₃ -/
def gellMann3 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0], ![0, -1, 0], ![0, 0, 0]]

/-- Gell-Mann matrix λ₄ -/
def gellMann4 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]]

/-- Gell-Mann matrix λ₅ -/
def gellMann5 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, -Complex.I], ![0, 0, 0], ![Complex.I, 0, 0]]

/-- Gell-Mann matrix λ₆ -/
def gellMann6 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]]

/-- Gell-Mann matrix λ₇ -/
def gellMann7 : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0, 0, 0], ![0, 0, -Complex.I], ![0, Complex.I, 0]]

/-- Gell-Mann matrix λ₈ (unnormalized) -/
def gellMann8_unnorm : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, -2]]

/-- su(2) structure constants: Levi-Civita symbol -/
def su2StructureConstant (a b c : Fin 3) : ℝ :=
  if (a, b, c) = (0, 1, 2) ∨ (a, b, c) = (1, 2, 0) ∨ (a, b, c) = (2, 0, 1) then 1
  else if (a, b, c) = (2, 1, 0) ∨ (a, b, c) = (1, 0, 2) ∨ (a, b, c) = (0, 2, 1) then -1
  else 0

/-- su(2) structure constants are totally antisymmetric -/
theorem su2StructureConstant_antisymm (a b c : Fin 3) :
    su2StructureConstant b a c = -su2StructureConstant a b c := by
  simp only [su2StructureConstant]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

/-- For N = 2, su(2) has noncommuting elements -/
theorem su2_has_noncommuting_pair :
    ∃ (A B : SuNAlgebra 2), ⁅A, B⁆ ≠ 0 :=
  ⟨su2Gen1, su2Gen2, su2_noncommutative⟩

/-- Embed a 2×2 matrix into the upper-left block of an (N+2)×(N+2) matrix -/
noncomputable def embedMatrix2 (M : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ :=
  fun i j =>
    if hi : i.val < 2 then
      if hj : j.val < 2 then
        M ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else 0

/-- Trace preservation for embedded matrix -/
theorem embedMatrix2_trace (M : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    trace (embedMatrix2 M N) = trace M := by
  simp only [trace, diag]
  -- Auxiliary lemma: only i.val < 2 gives nonzero contribution
  have key : ∀ i : Fin (N + 2), embedMatrix2 M N i i =
      if h : i.val < 2 then M ⟨i.val, h⟩ ⟨i.val, h⟩ else 0 := by
    intro i
    simp only [embedMatrix2]
    by_cases h : i.val < 2
    · simp only [h, dite_true]
    · simp only [h, dite_false]
  simp only [key]
  -- Expand the right-hand side
  rw [Fin.sum_univ_two]
  -- Extract the i = 0, 1 terms from the left-hand side sum
  have h0_lt : (0 : Fin (N + 2)).val < 2 := Nat.zero_lt_two
  have h1_lt : (1 : Fin (N + 2)).val < 2 := Nat.one_lt_two
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (0 : Fin (N + 2)))]
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp⟩ :
      (1 : Fin (N + 2)) ∈ Finset.univ \ {0})]
  simp only [h0_lt, h1_lt, dite_true]
  -- Show that the remaining sum is 0
  have hrest : ∑ i ∈ (Finset.univ \ {0}) \ {(1 : Fin (N + 2))},
      (if h : i.val < 2 then M ⟨i.val, h⟩ ⟨i.val, h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hi
    have hne0 : i ≠ 0 := hi.1
    have hne1 : i ≠ 1 := hi.2
    have hnotlt : ¬i.val < 2 := by
      by_contra hlt
      -- i.val < 2 and i ≠ 0 and i ≠ 1 is a contradiction
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with hv0 | hv1
      · exact hne0 (Fin.ext hv0)
      · exact hne1 (Fin.ext hv1)
    simp [hnotlt]
  rw [hrest, zero_add]
  -- M ⟨1, _⟩ ⟨1, _⟩ + M ⟨0, _⟩ ⟨0, _⟩ = M 0 0 + M 1 1
  have h0eq : (⟨(0 : Fin (N + 2)).val, h0_lt⟩ : Fin 2) = 0 := Fin.ext rfl
  have h1eq : (⟨(1 : Fin (N + 2)).val, h1_lt⟩ : Fin 2) = 1 := Fin.ext rfl
  simp only [h0eq, h1eq]
  ring

/-- Anti-Hermitian property preservation for embedded matrix -/
theorem embedMatrix2_antiHermitian (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : conjTranspose M = -M) (N : ℕ) :
    conjTranspose (embedMatrix2 M N) = -embedMatrix2 M N := by
  ext i j
  simp only [embedMatrix2, conjTranspose, transpose_apply, map_apply, neg_apply]
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
  · -- i < 2, j < 2
    simp only [hi, hj, dite_true]
    have hM' := congr_fun₂ hM ⟨i.val, hi⟩ ⟨j.val, hj⟩
    simp only [conjTranspose, transpose_apply, map_apply, neg_apply] at hM'
    exact hM'
  · -- i < 2, j ≥ 2
    simp only [hi, hj, dite_true, dite_false, star_zero, neg_zero]
  · -- i ≥ 2, j < 2
    simp only [hi, hj, dite_false, dite_true, star_zero, neg_zero]
  · -- i ≥ 2, j ≥ 2
    simp only [hi, hj, dite_false, star_zero, neg_zero]

/-- Embed an su(2) element into su(N+2) -/
noncomputable def embedSu2 (A : SuNAlgebra 2) (N : ℕ) : SuNAlgebra (N + 2) where
  matrix := embedMatrix2 A.matrix N
  trace_zero := by rw [embedMatrix2_trace]; exact A.trace_zero
  anti_hermitian := embedMatrix2_antiHermitian A.matrix A.anti_hermitian N

/-- Embedding preserves Lie bracket -/
theorem embedSu2_bracket (A B : SuNAlgebra 2) (N : ℕ) :
    ⁅embedSu2 A N, embedSu2 B N⁆ = embedSu2 ⁅A, B⁆ N := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, embedSu2]
  ext i j
  simp only [sub_apply, mul_apply, embedMatrix2]
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
  · -- i < 2, j < 2
    simp only [hi, hj, dite_true]
    -- Compute the components of the matrix product
    have h0_lt : (0 : Fin (N + 2)).val < 2 := Nat.zero_lt_two
    have h1_lt : (1 : Fin (N + 2)).val < 2 := Nat.one_lt_two
    have h_sum_AB : ∑ k : Fin (N + 2),
        (if hk : k.val < 2 then A.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
        (if hk : k.val < 2 then B.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) =
        ∑ k : Fin 2, A.matrix ⟨i.val, hi⟩ k * B.matrix k ⟨j.val, hj⟩ := by
      -- Extract only the k = 0, 1 terms
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (0 : Fin (N + 2)))]
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp⟩ :
          (1 : Fin (N + 2)) ∈ Finset.univ \ {0})]
      simp only [h0_lt, h1_lt, dite_true]
      -- The remaining sum is 0
      have hrest : ∑ k ∈ (Finset.univ \ {0}) \ {(1 : Fin (N + 2))},
          (if hk : k.val < 2 then A.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
          (if hk : k.val < 2 then B.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
        have hne0 : k ≠ 0 := hk.1
        have hne1 : k ≠ 1 := hk.2
        have hnotlt : ¬k.val < 2 := by
          by_contra hlt
          have hval : k.val = 0 ∨ k.val = 1 := by omega
          rcases hval with hv0 | hv1
          · exact hne0 (Fin.ext hv0)
          · exact hne1 (Fin.ext hv1)
        simp [hnotlt]
      rw [hrest, zero_add]
      rw [Fin.sum_univ_two]
      -- ⟨0, h0_lt⟩ = 0 and ⟨1, h1_lt⟩ = 1
      have h0eq : (⟨(0 : Fin (N + 2)).val, h0_lt⟩ : Fin 2) = 0 := Fin.ext rfl
      have h1eq : (⟨(1 : Fin (N + 2)).val, h1_lt⟩ : Fin 2) = 1 := Fin.ext rfl
      simp only [h0eq, h1eq]
      ring
    have h_sum_BA : ∑ k : Fin (N + 2),
        (if hk : k.val < 2 then B.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
        (if hk : k.val < 2 then A.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) =
        ∑ k : Fin 2, B.matrix ⟨i.val, hi⟩ k * A.matrix k ⟨j.val, hj⟩ := by
      -- Extract only the k = 0, 1 terms
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (0 : Fin (N + 2)))]
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp⟩ :
          (1 : Fin (N + 2)) ∈ Finset.univ \ {0})]
      simp only [h0_lt, h1_lt, dite_true]
      -- The remaining sum is 0
      have hrest : ∑ k ∈ (Finset.univ \ {0}) \ {(1 : Fin (N + 2))},
          (if hk : k.val < 2 then B.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
          (if hk : k.val < 2 then A.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
        have hne0 : k ≠ 0 := hk.1
        have hne1 : k ≠ 1 := hk.2
        have hnotlt : ¬k.val < 2 := by
          by_contra hlt
          have hval : k.val = 0 ∨ k.val = 1 := by omega
          rcases hval with hv0 | hv1
          · exact hne0 (Fin.ext hv0)
          · exact hne1 (Fin.ext hv1)
        simp [hnotlt]
      rw [hrest, zero_add]
      rw [Fin.sum_univ_two]
      -- ⟨0, h0_lt⟩ = 0 and ⟨1, h1_lt⟩ = 1
      have h0eq : (⟨(0 : Fin (N + 2)).val, h0_lt⟩ : Fin 2) = 0 := Fin.ext rfl
      have h1eq : (⟨(1 : Fin (N + 2)).val, h1_lt⟩ : Fin 2) = 1 := Fin.ext rfl
      simp only [h0eq, h1eq]
      ring
    rw [h_sum_AB, h_sum_BA]
  · -- i < 2, j ≥ 2
    simp only [hi, hj, dite_true, dite_false]
    -- if h : _ then 0 else 0 = 0 regardless of condition
    have hdite0 : ∀ k : Fin (N + 2), (if h : k.val < 2 then (0 : ℂ) else 0) = 0 := fun k => by
      split_ifs <;> rfl
    simp only [hdite0, mul_zero, sub_self, Finset.sum_const_zero]
  · -- i ≥ 2, j < 2
    simp only [hi, hj, dite_false, dite_true]
    have hdite0 : ∀ k : Fin (N + 2), (if h : k.val < 2 then (0 : ℂ) else 0) = 0 := fun k => by
      split_ifs <;> rfl
    simp only [zero_mul, sub_self, Finset.sum_const_zero]
  · -- i ≥ 2, j ≥ 2
    simp only [hi, hj, dite_false]
    have hdite0 : ∀ k : Fin (N + 2), (if h : k.val < 2 then (0 : ℂ) else 0) = 0 := fun k => by
      split_ifs <;> rfl
    simp only [hdite0, mul_zero, sub_self, Finset.sum_const_zero]

/-- Embedding preserves nonzero elements -/
theorem embedSu2_ne_zero (A : SuNAlgebra 2) (hA : A ≠ 0) (N : ℕ) :
    embedSu2 A N ≠ 0 := by
  intro h
  apply hA
  apply SuNAlgebra.ext
  have hM := congr_arg SuNAlgebra.matrix h
  simp only [embedSu2, SuNAlgebra.zero_matrix] at hM
  ext i j
  have hi : i.val < 2 := i.isLt
  have hj : j.val < 2 := j.isLt
  have hij : (embedMatrix2 A.matrix N) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = 0 := by
    rw [hM]; rfl
  simp only [embedMatrix2, hi, hj, dite_true] at hij
  convert hij

/-- For N ≥ 2, su(N) has noncommuting elements

Proof by embedding su(2) into su(N).
For N = 2, directly constructed from Pauli matrices.
For N > 2, we use embedding of su(2) into the upper-left 2×2 block.
-/
theorem exists_noncommuting_elements (N : ℕ) (hN : N ≥ 2) :
    ∃ (A B : SuNAlgebra N), ⁅A, B⁆ ≠ 0 := by
  match N, hN with
  | 2, _ => exact su2_has_noncommuting_pair
  | n + 3, _ =>
    -- Case N = n + 3 ≥ 3: embed su(2) into the upper-left 2×2 block of su(N)
    -- Since n + 3 = (n + 1) + 2, we can use embedSu2
    use embedSu2 su2Gen1 (n + 1)
    use embedSu2 su2Gen2 (n + 1)
    intro h
    -- Embedding preserves Lie bracket
    have hbracket := embedSu2_bracket su2Gen1 su2Gen2 (n + 1)
    rw [hbracket] at h
    -- Contradiction from the fact that embedSu2 preserves nonzero elements
    have hne : ⁅su2Gen1, su2Gen2⁆ ≠ 0 := su2_noncommutative
    have hne' : embedSu2 ⁅su2Gen1, su2Gen2⁆ (n + 1) ≠ 0 := embedSu2_ne_zero _ hne (n + 1)
    exact hne' h

end Newton
