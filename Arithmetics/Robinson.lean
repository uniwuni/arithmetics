import Arithmetics.Basic
import Mathlib.ModelTheory.Satisfiability
variable {α : Type*}

namespace FirstOrder

open FirstOrder

namespace Arith.Robinson

open Language arith Structure 

def axiom_succ_ne_zero : arith.Sentence :=
  ∀'(∼ (succ (&0) =' 0))

def axiom_succ_inj_of : arith.Sentence :=
  ∀'∀'(succ (&0) =' succ (&1) ⟹ &0 =' &1)

def axiom_add_zero : arith.Sentence :=
  ∀'((&0 + 0) =' &0)

def axiom_add_succ : arith.Sentence :=
  ∀'∀'((&0 + succ (&1)) =' succ (&0 + &1))

def axiom_mul_zero : arith.Sentence :=
  ∀'((&0 * 0) =' 0)

def axiom_mul_succ : arith.Sentence :=
  ∀'∀'((&0 * succ (&1)) =' ((&0 * &1) + &0))

def axiom_zero_or_succ : arith.Sentence :=
  ∀'(&0 =' 0 ⊔ ∃'(&0 =' succ &1))

def axiom_le_iff_ex_add : arith.Sentence :=
  ∀'∀'((&0 ≤'' &1) ⇔ ∃' ((&2 + &0) =' &1))

def axiom_succ_zero_eq_one : arith.Sentence :=
  (0 + 1) =' 1

def Q : arith.Theory :=
  {axiom_succ_ne_zero,
   axiom_succ_inj_of,
   axiom_add_zero,
   axiom_add_succ,
   axiom_mul_zero,
   axiom_mul_succ,
   axiom_zero_or_succ,
   axiom_le_iff_ex_add,
   axiom_succ_zero_eq_one}
  
section
open CompatibleOrderedSemiring

class RobinsonStructure (R : Type*) [Add R] [Mul R] [LE R] [One R] [Zero R] extends CompatibleOrderedSemiring R : Prop where
  succ_ne_zero {x : R} : x + 1 ≠ 0
  succ_inj_of {x y : R} (h : x + 1 = y + 1) : x = y
  add_zero (x : R) : x + 0 = x
  add_succ (x y : R) : x + (y + 1) = (x + y) + 1
  mul_zero (x : R) : x * 0 = 0
  mul_succ (x y : R) : x * (y + 1) = x * y + x
  zero_or_succ (x : R) : x = 0 ∨ ∃ z, x = z + 1
  le_iff_ex_add (x y : R) : x ≤ y ↔ ∃ (z : R), z + x = y
  succ_zero_eq_one : 0 + 1 = (1 : R)

end

variable {R : Type*} [Add R] [Mul R] [LE R] [One R] [Zero R] [CompatibleOrderedSemiring R]

theorem satisfies_robinson_iff : R ⊨ Q ↔ RobinsonStructure R
  := by
  simp only [Q, axiom_succ_ne_zero, Function.comp_apply, axiom_succ_inj_of, axiom_add_zero, axiom_add_succ, axiom_mul_zero,
    axiom_mul_succ, axiom_zero_or_succ, axiom_le_iff_ex_add, Set.mem_insert_iff, BoundedFormula.all.injEq,
    Set.mem_singleton_iff, false_or, Theory.model_iff, forall_eq_or_imp, forall_eq, ne_eq, axiom_succ_zero_eq_one]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8, h9⟩
    constructor
    · intro x
      specialize h1 x
      simp[h1, Fin.snoc] at h1
      exact h1
    · intro x y
      specialize h2 x y
      simp[h2, Fin.snoc] at h2
      exact h2
    · intro x
      specialize h3 x
      simp[h3, Fin.snoc] at h3
      exact h3
    · intro x y
      specialize h4 x y
      simp[h4, Fin.snoc] at h4
      exact h4
    · intro x
      specialize h5 x
      simp[h5, Fin.snoc] at h5
      exact h5
    · intro x y
      specialize h6 x y
      simp[h6, Fin.snoc] at h6
      exact h6
    · intro x
      specialize h7 x
      simp[h7, Fin.snoc] at h7
      exact h7
    · intro x y
      specialize h8 x y
      simp[h8, Fin.snoc] at h8
      exact h8
    · exact h9
  · intro h
    split_ands
    · intro x
      simp[Fin.snoc, h.succ_ne_zero]
    · intro x y
      simp[Fin.snoc]
      apply h.succ_inj_of
    · intro x
      simp[Fin.snoc, h.add_zero]
    · intro x y
      simp[Fin.snoc, h.add_succ]
    · intro x
      simp[Fin.snoc, h.mul_zero]
    · intro x y
      simp[Fin.snoc, h.mul_succ]
    · intro x
      simp[Fin.snoc, h.zero_or_succ]
    · intro x y
      simp[Fin.snoc, h.le_iff_ex_add]
    · exact h.succ_zero_eq_one

variable [RobinsonStructure R]
open RobinsonStructure
attribute [simp] FirstOrder.Arith.Robinson.RobinsonStructure.add_zero add_succ FirstOrder.Arith.Robinson.RobinsonStructure.mul_zero mul_succ succ_ne_zero succ_zero_eq_one


instance (n) : OfNat R n := 
  ⟨Term.realize (default : Empty → _) (ofNat' n)⟩

lemma ofNat_zero : OfNat.ofNat 0 = (Zero.zero : R) := by rfl

lemma ofNat_one : OfNat.ofNat 1 = (One.one : R) := by rfl


lemma ofNat_succ {n : ℕ} : OfNat.ofNat (n+1) = (OfNat.ofNat n) + (1 : R) := by rfl

instance (x : R) : NeZero (x + 1) := ⟨succ_ne_zero⟩

instance : NeZero (1 : R) := by
  rw[←succ_zero_eq_one]
  infer_instance

lemma succ_injective : Function.Injective (· + 1 : R → R) :=
  λ ⦃ _ _ ⦄ ↦ succ_inj_of
  
@[simp]
lemma succ_inj {x y : R} : x + 1 = y + 1 ↔ x = y :=
  ⟨succ_inj_of, congrArg (· + 1)⟩

lemma pred_def_aux (x : R) : ∃! y, ((x = 0 ∧ y = 0) ∨ (x ≠ 0 ∧ y + 1 = x)) := by
  rcases zero_or_succ x with (⟨eq⟩|⟨y, eq⟩)
  · simp[eq]
  · use y
    rw[eq]
    simp [succ_ne_zero]

noncomputable def pred (x : R) : R := Classical.choose (pred_def_aux x)

@[simp]
lemma pred_zero : pred 0 = (0 : R) := by
  have := (Classical.choose_spec (pred_def_aux (0 : R))).left
  unfold pred
  dsimp only at this
  rcases this with ⟨a⟩|⟨b⟩
  · exact a.right
  · have := b.right
    exfalso
    apply succ_ne_zero this

@[simp]
lemma pred_succ (x : R) : pred (x + 1) = x := by
  have := (Classical.choose_spec (pred_def_aux (x + 1 : R))).right x
  unfold pred
  dsimp only at this
  specialize this (Or.inr ⟨succ_ne_zero, rfl⟩)
  exact this.symm

@[simp]
lemma add_zero_iff_both (x y : R) : x + (y : R) = 0 ↔ (x = 0 ∧ y = 0) := by
  constructor
  · rcases zero_or_succ x with (⟨hx⟩|⟨px, hx⟩)
    · rw[hx]
      rcases zero_or_succ y with (⟨hy⟩|⟨py, hy⟩)
      · simp[hy]
      · simp[hy]        
    · rw[hx]
      rcases zero_or_succ y with (⟨hy⟩|⟨py, hy⟩)
      · simp[hy]
      · simp[hy] 
  . intro hx
    simp[hx]


lemma mul_zero_of_either_zero (x y : R) : x * (y : R) = 0 → (x = 0 ∨ y = 0) := by
  rcases zero_or_succ x with (⟨hx⟩|⟨px, hx⟩)
  · rw[hx]
    rcases zero_or_succ y with (⟨hy⟩|⟨py, hy⟩)
    · simp[hy]
    · simp[hy]        
  · rw[hx]
    rcases zero_or_succ y with (⟨hy⟩|⟨py, hy⟩)
    · simp[hy]
    · simp only [hy, mul_succ, add_succ, add_zero_iff_both, and_imp]
      intro _ _ h
      exfalso
      exact one_ne_zero h

@[simp]
lemma zero_le (x : R) : 0 ≤ x := by
  rw[le_iff_ex_add]
  use x
  simp

instance: Bot R := ⟨0⟩

instance: OrderBot R := ⟨zero_le⟩

lemma suc_le_iff_nat {n : ℕ} {x : R} (h : x + 1 ≤ OfNat.ofNat (n + 1)) : x ≤ OfNat.ofNat n := by
  cases n with
  | zero =>
    simp only [Nat.zero_eq]
    rw[ofNat_succ, le_iff_ex_add] at h
    rcases h with ⟨z, h⟩
    rw[le_iff_ex_add]
    use z
    simp only [add_succ, Nat.zero_eq, succ_zero_eq_one] at h
    apply succ_inj_of 
    simp[h]
  | succ n =>
    simp only [ofNat_succ]
    rw[ofNat_succ] at h
    rw[le_iff_ex_add] at h
    rcases h with ⟨z, h⟩
    rw[ofNat_succ] at h
    simp only [add_succ] at h 
    have h2 := succ_inj_of h
    rw[le_iff_ex_add]
    use z

@[simp]
lemma suc_add_left_nat (n : ℕ) (x : R) : (x + 1) + OfNat.ofNat n = x + OfNat.ofNat (n + 1) := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, RobinsonStructure.add_zero]
    rw[ofNat_succ, succ_zero_eq_one]
  | succ n ih =>
    rw[ofNat_succ]
    rw[ofNat_succ]
    simp only [add_succ]
    rw[ih]

@[simp]
lemma zero_add_left_nat (n : ℕ) : 0 + (OfNat.ofNat n : R) = (OfNat.ofNat n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw[ofNat_succ]
    simp[ih]

lemma eq_or_le_of_le_nat {n : ℕ} {x : R} (h : OfNat.ofNat n ≤ x) : 
   OfNat.ofNat n = x ∨ OfNat.ofNat (n + 1) ≤ x := by
  rw[le_iff_ex_add] at h
  rcases h with ⟨z, h⟩
  rcases zero_or_succ z with (⟨hz⟩|⟨pz, hz⟩)
  · rw[hz, zero_add_left_nat _] at h
    exact Or.inl h
  · right
    rw[ofNat_succ, ←h, hz, suc_add_left_nat, ofNat_succ, le_iff_ex_add]
    use pz
@[simp]
lemma ofNat_add (n m : ℕ) : (OfNat.ofNat (n + m) : R) = OfNat.ofNat n + OfNat.ofNat m
  := by
  induction m with
  | zero => simp
  | succ m' ih =>
    dsimp
    rw[ofNat_succ, add_succ, ← ih, Nat.add_succ, ofNat_succ]
@[simp]
lemma ofNat_mul (n m : ℕ) : (OfNat.ofNat (n * m) : R) = OfNat.ofNat n * OfNat.ofNat m 
  := by
  induction m with
  | zero => simp
  | succ m' ih =>
    dsimp
    rw[ofNat_succ, mul_succ, Nat.mul_succ, ofNat_add, ih]

lemma ofNat_inj' (n m : ℕ) (h : OfNat.ofNat n = (OfNat.ofNat m : R)) : n = m :=
  match n, m with
  | 0,  0 => rfl
  | n' + 1, 0 => by
       rw[ofNat_succ (R := R), ofNat_zero] at h
       exfalso
       apply succ_ne_zero h
  | 0, m' + 1 => by
       rw[ofNat_succ (R := R), ofNat_zero] at h
       exfalso
       apply succ_ne_zero h.symm
  | n' + 1, m' + 1 => by
       rw[ofNat_succ (R := R), ofNat_succ (R := R)] at h
       simp only [succ_inj] at h
       exact congr_arg _ (ofNat_inj' _ _ h)

@[simp]
lemma ofNat_inj {n m : ℕ} : OfNat.ofNat n = (OfNat.ofNat m : R) ↔ n = m :=
  ⟨ofNat_inj' n m, λ h ↦ by rw[h]⟩

lemma le_ofNat_iff : ∀ {n : ℕ} {x : R}, x ≤ OfNat.ofNat n ↔ ∃ m ≤ n, x = OfNat.ofNat m := by
  intro n 
  induction n with
  | zero =>
    simp only [Nat.zero_eq, le_iff_ex_add, add_zero_iff_both, exists_eq_left, nonpos_iff_eq_zero]
    rw[ofNat_zero]
  | succ n' ih =>
    intro x
    constructor
    · intro h
      rcases zero_or_succ x with (⟨hx⟩|⟨px, hx⟩)
      · rw[hx]
        use 0
        simp
      · rw[hx, ofNat_succ] at h 
        have h := suc_le_iff_nat h
        obtain ⟨m,eq1,eq2⟩ := ih.mp h
        use m + 1
        constructor
        · exact Nat.succ_le_succ eq1
        · rw[ofNat_succ, hx, eq2]
    · rintro ⟨m, m_le, m_eq⟩
      rw[m_eq]
      rw[le_iff_exists_add'] at m_le
      obtain ⟨c, eq⟩ := m_le
      rw[eq]
      rw[le_iff_ex_add]
      use OfNat.ofNat c
      simp[ofNat_add]

lemma ofNat_le_ofNat {n m : ℕ} : OfNat.ofNat n ≤ (OfNat.ofNat m : R) ↔ n ≤ m := by
  constructor
  · intro h
    rw[le_ofNat_iff] at h
    obtain ⟨p, le_p, eq_p⟩ := h
    simp only [ofNat_inj] at eq_p
    simp[eq_p, le_p]
  · intro h
    rw[le_iff_exists_add'] at h
    obtain ⟨c, eq⟩ := h
    rw[le_ofNat_iff]
    rw[eq]
    use n
    simp

lemma ofNat_le_total {n : ℕ} {x : R} : OfNat.ofNat n ≤ x ∨ x ≤ OfNat.ofNat n := by
  induction n with
  | zero => exact Or.inl bot_le
  | succ n' ih =>
    rcases ih with ih|ih
    · rcases zero_or_succ x with (⟨eq⟩|⟨px, eq⟩)
      · rw[eq]
        exact Or.inr bot_le
      · rw[eq] at ih
        rw[eq, ofNat_succ]
        have ih := eq_or_le_of_le_nat ih
        rcases ih with ih|ih
        · right
          rw[←ih, ← ofNat_succ, ofNat_le_ofNat]
          simp
        · left
          assumption
    · right
      rw[le_ofNat_iff]
      rw[le_ofNat_iff] at ih
      obtain ⟨m, m_le, m_eq⟩ := ih
      use m
      simp only [Nat.le_succ_of_le, and_self, *]
          



end Arith.Robinson

end FirstOrder
