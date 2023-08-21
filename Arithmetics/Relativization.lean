import Arithmetics.QBFormulas
import Arithmetics.Basic
namespace FirstOrder.Language

open FirstOrder.Language
open FirstOrder
open Language Structure 
variable {L : Language} {n : ℕ}

namespace Term

def liftAt' {n : ℕ} (n' : ℕ) : L.Term (Sum α (Fin n)) → L.Term (Sum α (Fin (n' + n))) :=
  relabel (Sum.map id fun i => Fin.natAdd n' i)
end Term


namespace BoundedFormula
variable (χ : L.BoundedFormula α 1)

def liftAt' : ∀ {n : ℕ} (n' : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n' + n) :=
  fun {n} n' φ =>
  φ.mapTermRel (fun k t => t.liftAt' n') (fun _ => id) fun _ =>
    castLE (by rw [add_assoc])


def relativize : {n : ℕ} → L.BoundedFormula α n → L.BoundedFormula α n
| _, falsum => falsum
| _, imp φ ψ => imp (relativize φ) (relativize ψ)
| _, rel r xs => rel r xs
| _, equal a b => equal a b
| n, all φ => all ((χ.liftAt' n) ⟹ (relativize φ))
end BoundedFormula
section
variable {R : Type*} [Structure L R]
namespace BoundedFormula

lemma Fin.append_snoc {m} (k1 : Fin n → α) (k2 : Fin m → α) (b : α) :
  (Fin.snoc (Fin.append k1 k2) b) = Fin.append k1 (Fin.snoc k2 b) := by
  have h: b = ![b] 0 := by simp
  rw[h, ← Fin.append_right_eq_snoc]
  rw[Fin.append_assoc]
  ext x
  simp
  rw[Fin.append_right_eq_snoc]
  congr


lemma Fin.natAdd_eq_last : ((Fin.natAdd n 0) : Fin (n+1)) = Fin.last n  := by 
          apply Fin.eq_of_val_eq
          simp 

lemma liftAt_append {m} (χ : L.BoundedFormula α m) (k1 k2 : _) : Realize (M := R) (liftAt' n χ) f (Fin.append k1 k2) ↔ Realize (M := R) χ f k2 := match χ with
  | ⊥ => by simp only [liftAt', mapTermRel, realize_bot, iff_false]; exact id
  | imp φ ψ => by simp[liftAt', mapTermRel]; rw[←liftAt', ←liftAt']; rw[liftAt_append φ, liftAt_append ψ]
  | rel r xs => by
    simp[liftAt', mapTermRel, Term.liftAt'];
    rw[Realize, Realize];
    simp only [Term.realize_relabel]
    have h : (Sum.elim f (Fin.append k1 k2) ∘ Sum.map id fun i => Fin.natAdd n i) = Sum.elim f k2 := by
      ext x
      rcases x with x|⟨l⟩
      · simp
      · simp
    rw[h]
  | equal x y => by
    simp only [liftAt'._eq_1, mapTermRel, Term.liftAt', Fin.coe_fin_one, lt_self_iff_false, ite_false]
    rw[Realize, Realize]
    simp only [Term.realize_relabel]
    have h : (Sum.elim f (Fin.append k1 k2) ∘ Sum.map id fun i => Fin.natAdd n i) = Sum.elim f k2 := by
      ext i
      rcases i with i|⟨a⟩
      · simp
      · simp
    rw[h]
  | all φ => by
    simp[liftAt', mapTermRel, Term.liftAt'];
    apply forall_congr'
    intro b
    rw[Fin.append_snoc]
    rw[← liftAt_append φ k1]
    have h : (mapTermRel (fun k t => Term.relabel (Sum.map id fun i => Fin.natAdd n i) t) (fun x => id)
        (fun x => castLE (liftAt'.proof_1 n x  : n + (x + 1) ≤ n + x + 1)) φ) = liftAt' n φ := by
      simp[liftAt', Term.liftAt']
    rw[← h]


@[simp] lemma liftAt_snoc (χ : L.BoundedFormula α 1) (k : _) : Realize (M := R) (liftAt' n χ) f (Fin.snoc k a) ↔ Realize (M := R) χ f (λ _ ↦ a) := by
  have h: a = ![a] 0 := by simp
  rw[h, ← Fin.append_right_eq_snoc]
  rw[liftAt_append]
  have : ![a] = λ _ ↦ a := by ext; simp
  rw[this]

lemma relativize_all_aux {φ : L.BoundedFormula α (n + 1)}  (χ : L.BoundedFormula α 1) (f : _) (k : _) :
  BoundedFormula.Realize (M := R)  (all ((χ.liftAt' n) ⟹ φ)) f k
    ↔ (∀ x, BoundedFormula.Realize (M := R) χ f (λ _ ↦ x) → BoundedFormula.Realize (M := R) φ f (Fin.snoc k x)) := by simp  
    
