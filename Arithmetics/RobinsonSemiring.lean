import Arithmetics.RobinsonModels
import Arithmetics.Relativization
variable {α : Type*}
namespace FirstOrder
namespace Arith.Robinson

open Language.Theory
open Language arith Structure 

section
variable {R : Type} [Add R] [Mul R] [LE R] [One R] [Zero R] [CompatibleOrderedSemiring R] {n : ℕ}
variable [RobinsonStructure R]
open RobinsonStructure
open CompatibleOrderedSemiring

local instance : R ⊨ Q := by rw[satisfies_robinson_iff]; infer_instance

namespace Relativizer
def addAssociativityForm (z : R) := ∀ x : R, ∀ y : R, (x + y) + z = x + (y + z)
def addAssociativityForm' : arith.Formula (Fin 1) := ∀'∀'(((&0 + &1) + var (Sum.inl 0)) =' (&0 + (&1 + var (Sum.inl 0))))
  

  

@[simp] lemma addAssociativityForm'_iff (z : R) :
  addAssociativityForm'.Realize (M := R) (λ _ ↦ z) ↔ addAssociativityForm z := by
  simp[addAssociativityForm',addAssociativityForm]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  simp[Fin.snoc]

@[simp] lemma addAssociativity_zero : addAssociativityForm 0 := by simp[addAssociativityForm]
lemma addAssociativity_succ {z : R} (h : addAssociativityForm z) : addAssociativityForm (z + 1) := by
  intro x y
  rw[add_succ, h, ← add_succ, ← add_succ]

lemma addAssociativity_pred {z : R} (h : addAssociativityForm z) : addAssociativityForm (pred z) := by
  intro x y
  simp only [addAssociativityForm, add_succ, succ_inj] at h 
  rcases zero_or_succ z with (⟨eq⟩|⟨z2, eq⟩)
  · rw[eq]; simp 
  · rw[eq]; simp; rw[← succ_inj, ← add_succ, ← eq, h, ← add_succ, ← add_succ, ← eq]

@[simp] lemma addAssociativity_add {z1 z2 : R} (h1 : addAssociativityForm z1) (h2 : addAssociativityForm z2) :
  addAssociativityForm (z1 + z2) := by
  intro x y
  unfold addAssociativityForm at h1 h2 
  rw[←h2,h1,h2,h2]


def distributivityForm (z : R) := ∀ x : R, ∀ y : R, addAssociativityForm x → x * (y + z) = x * y + x * z
/-- theres no way this genuinely worked what the hell -/
def distributivityForm' : arith.Formula (Fin 1) :=
  ∀'(BoundedFormula.relabel (λ _ ↦ (Sum.inr 0 : Fin 1 ⊕ Fin 1)) addAssociativityForm' ⟹ (∀' ((&0 * (&1 + var (Sum.inl 0))) =' ((&0 * &1) + (&0 * var (Sum.inl 0))))))
    



@[simp] lemma distributivityForm'_iff (z : R) :
  distributivityForm'.Realize (M := R) (λ _ ↦ z) ↔ distributivityForm z := by
  simp only [distributivityForm', Function.comp_apply, distributivityForm, addAssociativityForm']
  apply forall_congr'
  intro x
  simp only [BoundedFormula.relabel_all, Nat.add_eq, Nat.add_zero, Fin.snoc, Fin.coe_fin_one, lt_self_iff_false,
    Fin.castSucc_castLT, cast_eq, dite_false, BoundedFormula.realize_imp, BoundedFormula.realize_all, zero_add,
    Nat.lt_one_iff, dite_eq_ite, Fin.coe_castLT, BoundedFormula.realize_relabel, BoundedFormula.realize_bdEqual,
    realize_add, Term.realize_var, Sum.elim_inr, Function.comp_apply, ite_false, ite_true, Sum.elim_inl, realize_mul,
    addAssociativityForm]
  constructor
  · intro h y hy
    exact h hy y
  · intro h hx a
    exact h a hx
    



  
  
@[simp] lemma distributivity_zero : distributivityForm 0 := by simp[distributivityForm]
lemma distributivity_succ {z : R} (h : distributivityForm z) : distributivityForm (z + 1) := by
  intro x y h2
  rw[add_succ, mul_succ, h, h2, mul_succ]
  exact h2


def mulAssociativityForm (z : R) := ∀ x : R, ∀ y : R, addAssociativityForm x → distributivityForm y → (x * y) * z = x * (y * z) 
@[simp]
def mulAssociativity_zero : mulAssociativityForm 0 := by simp[mulAssociativityForm]

def mulAssociativity_succ {z : R} (h : mulAssociativityForm z) : mulAssociativityForm (z + 1) := by
  intro x y h1 h2
  rw[mul_succ, h, ← h2, mul_succ] 
  · exact h1
  · exact h1
  · exact h2


def zeroIdentityForm (z : R) := ∀ y : R, (0 : R) + y = z → y = z 
@[simp]
def zeroIdentity_zero : zeroIdentityForm 0 := by simp[zeroIdentityForm]

def zeroIdentity_succ {z : R} (h : zeroIdentityForm z) : zeroIdentityForm (z + 1) := by
  intro x y
  rcases zero_or_succ x with (⟨eq⟩|⟨x2, eq⟩)
  · simp only [eq, RobinsonStructure.add_zero] at y 
    exfalso
    exact succ_ne_zero y.symm
  · rw[eq] at y
    simp only [add_succ, succ_inj] at y 
    specialize h x2 y
    rwa[← h]

def zeroIdentity_prop {z : R} (h : zeroIdentityForm (0 + z)) : z = 0 + z := h z rfl

namespace Layers
variable (φ : arith.BoundedFormula Empty 1)
def c0 : 
end Layers
end Relativizers
end
end Arith.Robinson

end FirstOrder
