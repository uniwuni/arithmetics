import Arithmetics.Basic
import Mathlib.ModelTheory.Satisfiability
variable {α : Type*}

namespace FirstOrder

open FirstOrder

namespace Arith

open Language arith Structure 

def axiom_succ_ne_zero : arith.Sentence :=
  ∀'(∼ (succ (&0) =' 0))

def axiom_succ_inj : arith.Sentence :=
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
  ∀'∀'((&0 ≤'' &1) ⇔ ∃' ((&0 + &2) =' &1))

def robinson_arithmetic : arith.Theory :=
  {axiom_succ_ne_zero,
   axiom_succ_inj,
   axiom_add_zero,
   axiom_add_succ,
   axiom_mul_zero,
   axiom_mul_succ,
   axiom_zero_or_succ,
   axiom_le_iff_ex_add}
  
section

end
end Arith

end FirstOrder
