import Arithmetics.QBFormulas
import Arithmetics.Basic
namespace FirstOrder.Language

open FirstOrder.Language
open FirstOrder
open Language Structure 
variable {L : Language} {n : ℕ}
--variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
namespace Term
def liftAt' {n : ℕ} (n' m : ℕ) : L.Term (Sum α (Fin n)) → L.Term (Sum α (Fin (n' + n))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castLE (Nat.le_add_left n n') i else Fin.natAdd n' i)
end Term


namespace BoundedFormula
variable (χ : L.BoundedFormula α 1)

def liftAt' : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n' + n) :=
  fun {n} n' m φ =>
  φ.mapTermRel (fun k t => t.liftAt' n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc])

def relativize : {n : ℕ} → L.BoundedFormula α n → L.BoundedFormula α n
| _, falsum => falsum
| _, imp φ ψ => imp (relativize φ) (relativize ψ)
| _, rel r xs => rel r xs
| _, equal a b => equal a b
| n, all φ => all ((χ.liftAt' n 0) ⟹ (relativize φ))
end BoundedFormula
section
variable {R : Type*} [Structure L R]
namespace BoundedFormula
lemma relativize_all_aux {φ : L.BoundedFormula α (n + 1)}  (χ : L.BoundedFormula α 1) (f : _) (k : _) :
  BoundedFormula.Realize (M := R)  (all ((χ.liftAt' n 0) ⟹ φ)) f k
    ↔ (∀ x, BoundedFormula.Realize (M := R) χ f (λ _ ↦ x) → BoundedFormula.Realize (M := R) φ f (Fin.snoc k x)) :=
  match χ with
    | ⊥ => by
      simp only [realize_all, realize_imp]
      apply forall_congr'
      intro a
      simp only [liftAt', mapTermRel, realize_bot, IsEmpty.forall_iff, iff_true]
      intro h
      exfalso
      exact h      
    | imp χ₁ χ₂ => sorry
    | rel r xs => sorry
    | equal a b => sorry
    | all χ => sorry
    
    
    
example : ℕ := 1