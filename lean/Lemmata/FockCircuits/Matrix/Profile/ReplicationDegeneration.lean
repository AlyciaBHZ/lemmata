module

public import Lemmata.FockCircuits.Matrix.Profile.ReplicationFiltration
public import Lemmata.FockCircuits.Matrix.Convolution.CoordinateMaps
public import Lemmata.FockCircuits.Matrix.Character.Degeneration

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile.Replication

open Polynomial Foundation Spectral
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

theorem restrict_weighted_constants {ι κ η ι' κ' η' : Type*}
    [Fintype ι] [Fintype κ] [Fintype η]
    (T : Tensor K ι κ η) (A : ι' → ι → K) (B : κ' → κ → K)
    (C' : η' → η → K) (a : ι' → ℕ) (b : κ' → ℕ) (c : η' → ℕ)
    (x : ι') (y : κ') (z : η') :
    Tensor.restrict (fun x i => C (A x i) * X ^ a x)
      (fun y j => C (B y j) * X ^ b y) (fun z k => C (C' z k) * X ^ c z)
      (fun i j k => C (T i j k)) x y z =
      X ^ (a x + b y + c z) * C (Tensor.restrict A B C' T x y z) := by
  simp only [Tensor.restrict, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [map_mul, pow_add]
  ring

def lagrangeInput {q : ℕ} (nodes : Fin q → K) (P : K[X])
    {r : ℕ} (x : Fin q × Fin r) : K[X] :=
  Lagrange.basis Finset.univ nodes x.1 * P ^ x.2.val

theorem lagrangeInput_degree {q r : ℕ} (nodes : Fin q → K)
    (hnodes : Function.Injective nodes) (P : K[X]) (hdegree : P.natDegree = q)
    (x : Fin q × Fin r) : (lagrangeInput nodes P x).natDegree < q * r := by
  have hq : 0 < q := Nat.zero_lt_of_lt x.1.isLt
  have hb := Lagrange.natDegree_basis hnodes.injOn (Finset.mem_univ x.1)
  simp only [Finset.card_univ, Fintype.card_fin] at hb
  have hmul := natDegree_mul_le (p := Lagrange.basis Finset.univ nodes x.1)
    (q := P ^ x.2.val)
  rw [hb, natDegree_pow, hdegree] at hmul
  rw [Nat.mul_comm x.2.val q] at hmul
  have hqa := Nat.mul_le_mul_left q (Nat.succ_le_of_lt x.2.isLt)
  rw [Nat.mul_succ] at hqa
  dsimp [lagrangeInput]
  omega

def replicationLeft {q r : ℕ} (nodes : Fin q → K) (P : K[X])
    (x : Fin q × Fin r) (i : Fin (q * r)) : K[X] :=
  C ((lagrangeInput nodes P x).coeff i.val) * X ^ (r - 1 - x.2.val)

def replicationRight {q r s : ℕ} (nodes : Fin q → K) (P : K[X]) (hP : P.Monic)
    (z : Fin q × Fin (r + s - 1)) (k : Fin (q * r + q * s - 1)) : K[X] :=
  C (blockEvaluation P hP z.2.val (nodes z.1) (X ^ k.val)) * X ^ z.2.val

def replicationCarry {q r s : ℕ} (nodes : Fin q → K) (P : K[X]) :
    Tensor K (Fin q × Fin r) (Fin q × Fin s) (Fin q × Fin (r + s - 1)) :=
  fun x y z => if x.2.val + y.2.val + 1 = z.2.val then
    ((Lagrange.basis Finset.univ nodes x.1 *
      Lagrange.basis Finset.univ nodes y.1) /ₘ P).eval (nodes z.1) else 0

/-- The finite restriction is exactly a diagonal replicated convolution plus one higher-degree term. -/
theorem replication_restriction {q r s : ℕ} (nodes : Fin q → K)
    (hnodes : Function.Injective nodes) (P : K[X]) (hP : P.Monic)
    (hdegree : P.natDegree = q) (hroot : ∀ i, P.eval (nodes i) = 0)
    (x : Fin q × Fin r) (y : Fin q × Fin s) (z : Fin q × Fin (r + s - 1)) :
    Tensor.restrict (replicationLeft nodes P) (replicationLeft nodes P)
      (replicationRight nodes P hP)
      (fun i j k => C (convolution (K := K) (q * r) (q * s) i j k)) x y z =
      X ^ (r + s - 2) * C (Tensor.directSum (fun _ : Fin q => convolution r s) x y z) +
        X ^ (r + s - 1) * C (replicationCarry nodes P x y z) := by
  classical
  have hq : 0 < P.natDegree := by rw [hdegree]; exact Nat.zero_lt_of_lt x.1.isLt
  have hu (i : Fin q) : (Lagrange.basis Finset.univ nodes i).natDegree < P.natDegree := by
    rw [Lagrange.natDegree_basis hnodes.injOn (Finset.mem_univ i), hdegree]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  change Tensor.restrict
    (fun x i => C ((lagrangeInput nodes P x).coeff i.val) * X ^ (r - 1 - x.2.val))
    (fun y j => C ((lagrangeInput nodes P y).coeff j.val) * X ^ (s - 1 - y.2.val))
    (fun z k => C (blockEvaluation P hP z.2.val (nodes z.1) (X ^ k.val)) * X ^ z.2.val)
    (fun i j k => C (convolution (K := K) (q * r) (q * s) i j k)) x y z = _
  rw [restrict_weighted_constants]
  have hmap := convolution_coordinate_restriction
    (fun x : Fin q × Fin r => lagrangeInput nodes P x)
    (fun y : Fin q × Fin s => lagrangeInput nodes P y)
    (fun z : Fin q × Fin (r + s - 1) => blockEvaluation P hP z.2.val (nodes z.1))
    (lagrangeInput_degree nodes hnodes P hdegree)
    (lagrangeInput_degree nodes hnodes P hdegree)
  rw [congrFun (congrFun (congrFun hmap x) y) z]
  dsimp only [lagrangeInput]
  rw [filtered_block_product P _ _ hP hq x.2.isLt y.2.isLt z.2.val
    (nodes z.1) (hu x.1) (hu y.1) (hroot z.1)]
  congr 2
  · have heval (i : Fin q) : (Lagrange.basis Finset.univ nodes i).eval (nodes z.1) =
        if i = z.1 then 1 else 0 := by
      by_cases hiz : i = z.1
      · subst i
        simp only [ite_true]
        exact Lagrange.eval_basis_self hnodes.injOn (Finset.mem_univ z.1)
      · rw [if_neg hiz]
        exact Lagrange.eval_basis_of_ne hiz (Finset.mem_univ z.1)
    rw [heval x.1, heval y.1]
    have htag : (x.1 = z.1 ∧ y.1 = z.1) ↔ (x.1 = y.1 ∧ x.1 = z.1) := by
      constructor
      · rintro ⟨hx, hy⟩
        exact ⟨hx.trans hy.symm, hx⟩
      · rintro ⟨hxy, hx⟩
        exact ⟨hx, hxy.symm.trans hx⟩
    simp only [Tensor.directSum, convolution, ← htag]
    split_ifs <;> simp_all

theorem constant_mul_X_pow_degree_le (a : K) {n N : ℕ} (hn : n ≤ N) :
    (C a * X ^ n).degree ≤ (N : WithBot ℕ) := by
  apply degree_le_of_natDegree_le
  have h : (C a * X ^ n).natDegree ≤ n := by
    simpa only [natDegree_C, natDegree_X_pow, zero_add] using
      (natDegree_mul_le (p := C a) (q := X ^ n))
  exact h.trans hn

/-- Replication is an actual polynomial restriction with uniformly bounded map degrees. -/
def replicationDegeneration {q r s : ℕ} (nodes : Fin q → K)
    (hnodes : Function.Injective nodes) (P : K[X]) (hP : P.Monic)
    (hdegree : P.natDegree = q) (hroot : ∀ i, P.eval (nodes i) = 0) :
    Tensor.PolynomialRestrictionDegeneration (convolution (K := K) (q * r) (q * s))
      (Tensor.directSum (fun _ : Fin q => convolution r s)) (r + s - 2) r s (r + s) where
  leftMap := replicationLeft nodes P
  middleMap := replicationLeft nodes P
  rightMap := replicationRight nodes P hP
  left_degree := fun x i => constant_mul_X_pow_degree_le _ (by omega)
  middle_degree := fun y j => constant_mul_X_pow_degree_le _ (by omega)
  right_degree := fun z k => constant_mul_X_pow_degree_le _ (by have hz := z.2.isLt; omega)
  vanishes := by
    intro x y z j hj
    rw [replication_restriction nodes hnodes P hP hdegree hroot]
    have hj' : j < r + s - 1 := by
      have hr := x.2.isLt
      have hs := y.2.isLt
      omega
    simp only [coeff_add, coeff_X_pow_mul', Nat.not_le.mpr hj,
      Nat.not_le.mpr hj', ite_false, add_zero]
  leading := by
    intro x y z
    rw [replication_restriction nodes hnodes P hP hdegree hroot]
    have hnext : ¬ r + s - 1 ≤ r + s - 2 := by
      have hr := x.2.isLt
      have hs := y.2.isLt
      omega
    simp only [coeff_add, coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self,
      coeff_C_zero, hnext, ite_false, add_zero]

def convolutionReplication [Infinite K] (q r s : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (convolution (K := K) (q * r) (q * s))
      (Tensor.directSum (fun _ : Fin q => convolution r s)) (r + s - 2) r s (r + s) := by
  let nodes : Fin q → K := fun i => Infinite.natEmbedding K i.val
  have hnodes : Function.Injective nodes := by
    intro i j h
    exact Fin.ext ((Infinite.natEmbedding K).injective h)
  exact replicationDegeneration nodes hnodes (Lagrange.nodal Finset.univ nodes)
    Lagrange.nodal_monic (by simp only [Lagrange.natDegree_nodal,
      Finset.card_univ, Fintype.card_fin])
    (fun i => Lagrange.eval_nodal_at_node (Finset.mem_univ i))

/-- The convolution profile can be replicated by every integer, in every characteristic. -/
theorem value_convolution_replicate [Infinite K] (χ : Character K) (q r s : ℕ) :
    (q : ℝ) * χ.value (convolution r s) ≤ χ.value (convolution (q * r) (q * s)) := by
  have h := χ.value_polynomialRestrictionDegeneration_le
    (convolutionReplication (K := K) q r s)
  simpa only [χ.map_directSum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

end

end Lemmata.FockCircuits.Matrix.Profile.Replication
