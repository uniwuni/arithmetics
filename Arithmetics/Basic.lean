import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Order
import Mathlib.Tactic.FinCases
variable {α : Type*}

namespace FirstOrder

open FirstOrder

/-- The type of Robinson arithmetic functions, to be used in the definition of the language of rings.
It contains the operations (+,*,-,0,1) -/
inductive arithFunc : ℕ → Type
  | add : arithFunc 2
  | mul : arithFunc 2
  | zero : arithFunc 0
  | one : arithFunc 0
  deriving DecidableEq

inductive arithRel : ℕ → Type
  | le : arithRel 2
  deriving DecidableEq

def Language.arith : Language :=
  { Functions := arithFunc,
    Relations := arithRel }

namespace Arith

open arithFunc arithRel Language

instance isOrderedArith : IsOrdered arith := ⟨le⟩

instance (n : ℕ) : DecidableEq (Language.arith.Functions n) := by
  dsimp [Language.arith]; infer_instance

instance (n : ℕ) : DecidableEq (Language.arith.Relations n) := by
  dsimp [Language.arith]; infer_instance

/-- `RingFunc.add`, but with the defeq type `Language.ring.Functions 2` instead
of `RingFunc 2` -/
abbrev addFunc : Language.arith.Functions 2 := add

/-- `RingFunc.mul`, but with the defeq type `Language.ring.Functions 2` instead
of `RingFunc 2` -/
abbrev mulFunc : Language.arith.Functions 2 := mul

/-- `RingFunc.zero`, but with the defeq type `Language.ring.Functions 0` instead
of `RingFunc 0` -/
abbrev zeroFunc : Language.arith.Functions 0 := zero

/-- `RingFunc.zero`, but with the defeq type `Language.ring.Functions 0` instead
of `RingFunc 0` -/
abbrev oneFunc : Language.arith.Functions 0 := one
@[simp]
abbrev leRel : Language.arith.Relations 2 := le

instance (α : Type*) : Zero (Language.arith.Term α) :=
{ zero := Constants.term zeroFunc }

theorem zero_def (α : Type*) : (0 : Language.arith.Term α) = Constants.term zeroFunc := rfl

instance (α : Type*) : One (Language.arith.Term α) :=
{ one := Constants.term oneFunc }

theorem one_def (α : Type*) : (1 : Language.arith.Term α) = Constants.term oneFunc := rfl

instance (α : Type*) : Add (Language.arith.Term α) :=
{ add := addFunc.apply₂ }

theorem add_def (α : Type*) (t₁ t₂ : Language.arith.Term α) :
    t₁ + t₂ = addFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Mul (Language.arith.Term α) :=
{ mul := mulFunc.apply₂ }

theorem mul_def (α : Type*) (t₁ t₂ : Language.arith.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ := rfl

def succ {α : Type*} (t : Language.arith.Term α) := t + 1

theorem succ_def (α : Type*) (t : Language.arith.Term α) :
    Arith.succ t = t + 1 := rfl

infix:55 " ≤'' " => leRel.boundedFormula₂

infix:55 " ≤' " => leRel.formula₂

theorem le_def (α : Type*) (t₁ t₂ : Language.arith.Term α) :
  t₁ ≤' t₂ = leRel.formula₂ t₁ t₂ := rfl

def ofNat' : ℕ → Language.arith.Term α
  | 0 => 0
  | (n + 1) => succ (ofNat' n)

instance : Fintype Language.arith.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .add⟩,
       Sum.inl ⟨2, .mul⟩,
       Sum.inl ⟨0, .one⟩,
       Sum.inl ⟨0, .zero⟩,
       Sum.inr ⟨2, .le⟩], by
    dsimp [Language.Symbols]; decide⟩, by
    intro x
    dsimp [Language.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    · cases f <;> decide
    · cases f; decide ⟩

@[simp]
theorem card_arith : card Language.arith = 5 := by
  have : Fintype.card Language.arith.Symbols = 5 := rfl
  simp [Language.card, this]

open Language arith Structure   


/-- A Type `R` is a `CompatibleRing` if it is structure for the language of rings and this structure
is the same as the structure already given on `R` by the classes `Add`, `Mul` etc.

It is recommended to use this type class as a hypothesis to any theorem whose statement
requires a type to have be both a `Ring` (or `Field` etc.) and a
`Language.ring.Structure`  -/
/- This class does not extend `Add` etc, because this way it can be used in
combination with a `Ring`, or `Field` instance without having multiple different
`Add` structures on the Type. -/
class CompatibleOrderedSemiring (R : Type*) [Add R] [Mul R] [One R] [Zero R] [LE R] [Language.arith.Structure R]
    : Prop where
  /-- Addition in the `Language.ring.Structure` is the same as the addition given by the
    `Add` instance -/
  
  ( funMap_add : ∀ x, (funMap addFunc x : R) = x 0 + x 1 )
  /-- Multiplication in the `Language.ring.Structure` is the same as the multiplication given by the
    `Mul` instance -/
  ( funMap_mul : ∀ x, (funMap mulFunc x : R) = x 0 * x 1 )
  /-- The constant `0` in the `Language.ring.Structure` is the same as the constant given by the
    `Zero` instance -/
  ( funMap_zero : ∀ x, funMap (zeroFunc : Language.arith.Constants) x = (0 : R) )
  /-- The constant `1` in the `Language.ring.Structure` is the same as the constant given by the
    `One` instance -/
  ( funMap_one : ∀ x, funMap (oneFunc : Language.arith.Constants) x = (1 : R) )

  ( relMap_le : ∀ x, RelMap leRel x = ((x 0 : R) ≤ x 1) )

open CompatibleOrderedSemiring

attribute [simp] funMap_add funMap_mul funMap_zero funMap_one relMap_le

section

variable {R : Type*} [Add R] [Mul R] [LE R] [One R] [Zero R] [Language.arith.Structure R] [CompatibleOrderedSemiring R]

theorem orderedStructureOfCompatibleOrderedSemiring : 
  Language.arith.OrderedStructure R := by
  rw [orderedStructure_iff]
  constructor
  · have := IsRelational.empty_functions (L := Language.order)
    intro n f
    exact (this n).elim' f
  · intro n r x
    let 2 := n
    have: r = leSymb := by cases r; rfl
    simp only [isOrderedArith, this, orderLHom_leSymb, relMap_le, eq_iff_iff]
    have: x = ![x 0, x 1] := by
      ext a
      fin_cases a <;> simp
    rw[this, relMap_leSymb]
    simp

@[simp]
theorem realize_add (x y : arith.Term α) (v : α → R) :
    Term.realize v (x + y) = Term.realize v x + Term.realize v y := by
  simp [add_def, funMap_add]

@[simp]
theorem realize_mul (x y : arith.Term α) (v : α → R) :
    Term.realize v (x * y) = Term.realize v x * Term.realize v y := by
  simp [mul_def, funMap_mul]

@[simp]
theorem realize_zero (v : α → R) : Term.realize v (0 : arith.Term α) = 0 := by
  simp [zero_def, funMap_zero, constantMap]

@[simp]
theorem realize_one (v : α → R) : Term.realize v (1 : arith.Term α) = 1 := by
  simp [one_def, funMap_one, constantMap]

@[simp]
theorem realize_succ (x : arith.Term α) (v : α → R) :
    Term.realize v (succ x) = Term.realize v x + 1 := by
  simp [succ_def, funMap_add, realize_add]

@[simp]
theorem realize_le (x y : arith.Term α) (v : α → R) :
    Formula.Realize (x ≤' y) v = (Term.realize v x ≤ Term.realize v y) := by
  simp


end

/-- Given a Type `R` with instances for each of the `Ring` operations, make a
`Language.ring.Structure R` instance, along with a proof that the operations given
by the `Language.ring.Structure` are the same as those given by the `Add` or `Mul` etc.
instances.

This definition can be used when applying a theorem about the model theory of rings
to a literal ring `R`, by writing `letI := compatibleRingOfRing R`. After this, if,
for example, `R` is a field, then Lean will be able to find the instance for
`Theory.field.Model R`, and it will be possible to apply theorems about the model theory
of fields.

This is a `def` and not an `instance`, because the path
`Ring` => `Language.ring.Structure` => `Ring` cannot be made to
commute by definition
-/
instance arithStructureOfOrderedSemiring (R : Type*) [Add R] [Mul R] [LE R] [One R] [Zero R] :
    Language.arith.Structure R :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1
    RelMap := fun {n} f =>
      match n, f with
      | _, .le => fun x => x 0 ≤ x 1}

instance compatibleOrderedSemiringOfOrderedSemiring (R : Type*) [Add R] [Mul R] [LE R] [One R] [Zero R] :
    CompatibleOrderedSemiring R :=
  {funMap_add := fun _ => rfl,
   funMap_mul := fun _ => rfl,
   funMap_zero := fun _ => rfl,
   funMap_one := fun _ => rfl,
   relMap_le := fun _ => rfl}
   
instance natCompatibleOrderedSemiring : CompatibleOrderedSemiring ℕ :=
  compatibleOrderedSemiringOfOrderedSemiring ℕ

variable (R : Type*) [Language.arith.Structure R]

/-- A def to put an `Add` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
@[reducible] def addOfArithStructure : Add R :=
  { add := fun x y => funMap addFunc ![x, y] }

/-- A def to put an `Mul` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
@[reducible] def mulOfArithStructure : Mul R :=
  { mul := fun x y => funMap mulFunc ![x, y] }

/-- A def to put an `Zero` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
@[reducible] def zeroOfArithStructure : Zero R :=
  { zero := funMap zeroFunc ![] }

/-- A def to put an `One` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
@[reducible] def oneOfArithStructure : One R :=
  { one := funMap oneFunc ![] }

@[reducible] def leOfArithStructure : LE R :=
  { le := fun x y => RelMap leRel ![x, y] }

attribute [local instance] addOfArithStructure mulOfArithStructure
  zeroOfArithStructure oneOfArithStructure leOfArithStructure

/--
Given a Type `R` with a `Language.ring.Structure R`, the instance given by
`addOfRingStructure` etc are compatible with the `Language.ring.Structure` instance on `R`.

This definition is only to be used when `addOfRingStructure`, `mulOfRingStructure` etc
are local instances.
-/
@[reducible] def compatibleOrderedSemiRingOfArithStructure : CompatibleOrderedSemiring R :=
  { funMap_add := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_mul := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_zero := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_one := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    relMap_le := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl  }

end Arith

end FirstOrder
