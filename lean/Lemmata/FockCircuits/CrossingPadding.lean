module

public import Lemmata.FockCircuits.CrossingAlgorithms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CrossingAlgorithms.AllOrders

noncomputable section

variable {R A B C A' B' C' : Type*} [CommSemiring R]
variable [Fintype A] [Fintype B] [Fintype C] [Fintype A'] [Fintype B'] [Fintype C']

def restrict (p : AllOrders R A B C) (a : A' ↪ A) (b : B' ↪ B) (c : C' ↪ C) :
    AllOrders R A' B' C' where
  abc := Matrix.OrderedMatrixAlgorithm.pad p.abc a b c
  acb := Matrix.OrderedMatrixAlgorithm.pad p.acb a c b
  bac := Matrix.OrderedMatrixAlgorithm.pad p.bac b a c
  bca := Matrix.OrderedMatrixAlgorithm.pad p.bca b c a
  cab := Matrix.OrderedMatrixAlgorithm.pad p.cab c a b
  cba := Matrix.OrderedMatrixAlgorithm.pad p.cba c b a

theorem bounded_restrict (p : AllOrders R A B C) (a : A' ↪ A) (b : B' ↪ B) (c : C' ↪ C)
    {t : ℝ} (hp : p.Bounded t) : (p.restrict a b c).Bounded t := by
  simpa only [Bounded, restrict, Matrix.OrderedMatrixAlgorithm.size_pad] using hp

def restrictModes {W V : ℕ} {S : Type*} [Fintype S]
    (p : AllOrders R (Fin V × S) B C) (hWV : W ≤ V) : AllOrders R (Fin W × S) B C :=
  p.restrict ((Fin.castLEEmb hWV).prodMap (Function.Embedding.refl S))
    (Function.Embedding.refl B) (Function.Embedding.refl C)

theorem bounded_restrictModes {W V : ℕ} {S : Type*} [Fintype S]
    (p : AllOrders R (Fin V × S) B C) (hWV : W ≤ V) {t : ℝ} (hp : p.Bounded t) :
    (p.restrictModes hWV).Bounded t :=
  p.bounded_restrict _ _ _ hp

end

end Lemmata.FockCircuits.CrossingAlgorithms.AllOrders

namespace Lemmata.FockCircuits.CrossingPadding

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommSemiring R]

abbrev Variables (n : ℕ) (J K : Type*) := Bool × (Fin n ⊕ (J × K))

def crossingPolynomial (n : ℕ) (J K : Type*) [Fintype J] [Fintype K] :
    FreeAlgebra R (Variables n J K) :=
  batchedCrossing
    (fun i => FreeAlgebra.ι R (true, Sum.inl i))
    (fun i => FreeAlgebra.ι R (false, Sum.inl i))
    (Matrix.of (fun j k => FreeAlgebra.ι R (true, Sum.inr (j, k))))
    (Matrix.of (fun j k => FreeAlgebra.ι R (false, Sum.inr (j, k))))

def identityQuartic (n : ℕ) : FreeAlgebra R (Fin n ⊕ Fin n) :=
  ∑ i, ∑ j, FreeAlgebra.ι R (Sum.inl i) * FreeAlgebra.ι R (Sum.inr j) *
    FreeAlgebra.ι R (Sum.inl i) * FreeAlgebra.ι R (Sum.inr j)

/-- Variable identification and zero padding are wiring and create no arithmetic gates. -/
def identifyBank {n : ℕ} {J K : Type*} [Fintype J] [Fintype K] (e : Fin n ↪ J × K) :
    CircuitFamily R (Fin n ⊕ Fin n) (Variables n J K) :=
  ((Matrix.CircuitBuilders.family (fun i : Fin n =>
      Matrix.CircuitBuilders.input (R := R) (Sum.inl i))).combine
    ((Matrix.paddingBank (K := R) e).mapInputs Sum.inr)).reindexOutputs Prod.snd

theorem size_identifyBank {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) : (identifyBank (R := R) e).size = 0 := by
  simp [identifyBank, Matrix.size_paddingBank]

theorem polynomial_identifyBank_left {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (b : Bool) (i : Fin n) :
    (identifyBank (R := R) e).polynomial (b, Sum.inl i) = FreeAlgebra.ι R (Sum.inl i) := by
  simp [identifyBank, CircuitFamily.polynomial]

theorem polynomial_identifyBank_right {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (b : Bool) (j : J) (k : K) :
    (identifyBank (R := R) e).polynomial (b, Sum.inr (j, k)) =
      Function.extend e (fun i => FreeAlgebra.ι R (Sum.inr i)) (fun _ => 0) (j, k) := by
  change (identifyBank (R := R) e).eval (algebraMap R _) (FreeAlgebra.ι R)
    (b, Sum.inr (j, k)) = _
  simp only [identifyBank, CircuitFamily.eval_reindexOutputs, CircuitFamily.eval_combine_inr,
    CircuitFamily.eval_mapInputs]
  exact congrFun (Matrix.eval_paddingBank e (fun i => FreeAlgebra.ι R (Sum.inr i))) (j, k)

theorem padded_crossing {A : Type*} [Semiring A] {n : ℕ} {J K : Type*}
    [Fintype J] [Fintype K] (e : Fin n ↪ J × K) (x y : Fin n → A) :
    batchedCrossing x x
      (Matrix.of (fun j k => Function.extend e y (fun _ => 0) (j, k)))
      (Matrix.of (fun j k => Function.extend e y (fun _ => 0) (j, k))) =
      ∑ i, ∑ j, x i * y j * x i * y j := by
  classical
  simp only [batchedCrossing, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Fintype.sum_prod_type (fun p : J × K =>
    x i * Function.extend e y (fun _ => 0) p * x i * Function.extend e y (fun _ => 0) p)]
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro p hp
    have hnot : ¬ ∃ j, e j = p := hp
    rw [Function.extend_apply' _ _ _ hnot]
    simp only [mul_zero]
  · intro j
    simp only [e.injective.extend_apply]

theorem polynomial_identify {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (c : CircuitFamily R (Variables n J K) PUnit)
    (hc : c.polynomial PUnit.unit = crossingPolynomial (R := R) n J K) :
    ((identifyBank (R := R) e).substitute c).polynomial PUnit.unit = identityQuartic (R := R) n := by
  rw [CircuitFamily.polynomial_substitute, hc]
  simp only [crossingPolynomial, batchedCrossing, map_sum, map_mul,
    FreeAlgebra.lift_ι_apply, Matrix.of_apply,
    polynomial_identifyBank_left, polynomial_identifyBank_right]
  change batchedCrossing (fun i => FreeAlgebra.ι R (Sum.inl i))
      (fun i => FreeAlgebra.ι R (Sum.inl i))
      (Matrix.of (fun j k => Function.extend e (fun i => FreeAlgebra.ι R (Sum.inr i))
        (fun _ => 0) (j, k)))
      (Matrix.of (fun j k => Function.extend e (fun i => FreeAlgebra.ι R (Sum.inr i))
        (fun _ => 0) (j, k))) = _
  exact padded_crossing e _ _

theorem hasCircuit_identify {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (c : CircuitFamily R (Variables n J K) PUnit)
    (hc : c.polynomial PUnit.unit = crossingPolynomial (R := R) n J K) :
    HasCircuit (identityQuartic (R := R) n) c.size := by
  let d := (identifyBank (R := R) e).substitute c
  refine ⟨d.nodeCount, d.circuit, d.output PUnit.unit, polynomial_identify e c hc, ?_⟩
  change d.size ≤ c.size
  simp only [d, CircuitFamily.size_substitute, size_identifyBank, zero_add, le_refl]

def capacityEmbedding {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (h : n ≤ Fintype.card J * Fintype.card K) : Fin n ↪ J × K :=
  (Fin.castLEEmb (by simpa only [Fintype.card_prod] using h)).trans
    (Fintype.equivFin (J × K)).symm.toEmbedding

theorem batch_capacity (n m : ℕ) (hm : 0 < m) : n ≤ m * batchCount n m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (div_le_iff₀ hmR).mp (Nat.le_ceil ((n : ℝ) / m))
  have h' : (n : ℝ) ≤ ((m * batchCount n m : ℕ) : ℝ) := by
    simpa only [batchCount, Nat.cast_mul, mul_comm] using h
  exact_mod_cast h'

def batchEmbedding (n E : ℕ) :
    Fin n ↪ (↥(fullCutoff E) × Fin (batchCount n (stateCount E))) :=
  capacityEmbedding (by
    simpa only [Fintype.card_coe, Fintype.card_fin, stateCount] using
      batch_capacity n (stateCount E) (stateCount_pos E))

/-- An eventual arithmetic bound extends to every positive size by changing its constant. -/
theorem uniform_bound_of_eventually {X : ℕ → Type*}
    (p : ∀ n, FreeAlgebra R (X n)) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ᶠ n : ℕ in Filter.atTop,
      ∃ s : ℕ, HasCircuit (p n) s ∧ (s : ℝ) ≤ (n : ℝ) ^ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (p n) s ∧ (s : ℝ) ≤ C * (n : ℝ) ^ L := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  choose size hsize using fun n => exists_circuit (p n)
  let C : ℕ := 1 + ∑ i : Fin N, size i
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by dsimp [C]; omega)
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, fun n hn => ?_⟩
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ L := Real.one_le_rpow (by exact_mod_cast hn) hL
  by_cases hlarge : N ≤ n
  · obtain ⟨s, hs, hcost⟩ := hN n hlarge
    refine ⟨s, hs, hcost.trans ?_⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (zero_le_one.trans hpow)
  · have hnN : n < N := by omega
    have hterm : size n ≤ ∑ i : Fin N, size i :=
      Finset.single_le_sum (f := fun i : Fin N => size i.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨n, hnN⟩ : Fin N))
    have hsmall : (size n : ℝ) ≤ C := by exact_mod_cast (show size n ≤ C by dsimp [C]; omega)
    refine ⟨size n, hsize n, hsmall.trans ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hC)

end

end Lemmata.FockCircuits.CrossingPadding
