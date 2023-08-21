import Arithmetics.QBFormulas
import Mathlib.ModelTheory.Substructures
import Mathlib.Tactic.FinCases
namespace FirstOrder.Language

open FirstOrder.Language
open FirstOrder
open Language Structure 
variable {L : Language} {n : ℕ} {α : Type*}

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


@[simp] def relativize : {n : ℕ} → L.BoundedFormula α n → L.BoundedFormula α n
| _, falsum => falsum
| _, imp φ ψ => imp (relativize φ) (relativize ψ)
| _, rel r xs => rel r xs
| _, equal a b => equal a b
| n, all φ => all ((χ.liftAt' n) ⟹ (relativize φ))
end BoundedFormula
section
variable {R : Type*} [Structure L R]
namespace BoundedFormula
@[simp] lemma BoundedFormula.realize_falsum {n} (f : α → R) (k : Fin n → R) : Realize (L := L) (M := R) falsum f k ↔ False := by rfl
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

@[simp]
lemma relativize_all_aux {φ : L.BoundedFormula α (n + 1)}  (χ : L.BoundedFormula α 1) (f : _) (k : _) :
  BoundedFormula.Realize (M := R) (all ((χ.liftAt' n) ⟹ φ)) f k
    ↔ (∀ x, BoundedFormula.Realize (M := R) χ f (λ _ ↦ x) → BoundedFormula.Realize (M := R) φ f (Fin.snoc k x)) := by simp  

lemma relativize_ex' {φ : L.BoundedFormula α (n + 1)}  (χ : L.BoundedFormula α 1) (f : _) (k : _) :
  BoundedFormula.Realize (M := R) ((relativize χ φ.ex) ⇔ ((χ.liftAt' n) ⊓ relativize χ φ).ex) f k := by
  rw[BoundedFormula.ex]
  simp only [relativize, realize_iff, realize_imp, realize_all, liftAt_snoc, BoundedFormula.realize_falsum, realize_ex,
    realize_inf]
  rw[← not_exists_not]
  simp

@[simp]
lemma relativize_ex {φ : L.BoundedFormula α (n + 1)}  (χ : L.BoundedFormula α 1) (f : _) (k : _) :
  BoundedFormula.Realize (M := R) (relativize χ φ.ex) f k ↔ BoundedFormula.Realize (M := R) ((χ.liftAt' n) ⊓ relativize χ φ).ex f k := by
  rw[BoundedFormula.ex]
  simp only [relativize, realize_iff, realize_imp, realize_all, liftAt_snoc, BoundedFormula.realize_falsum, realize_ex,
    realize_inf]
  rw[← not_exists_not]
  simp


@[simp]
lemma relativize_ex_aux {φ : L.BoundedFormula α (n + 1)}  (χ : L.BoundedFormula α 1) (f : _) (k : _) :
  BoundedFormula.Realize (M := R) ((χ.liftAt' n) ⊓ φ).ex f k
    ↔ (∃ x, BoundedFormula.Realize (M := R) χ f (λ _ ↦ x) ∧ BoundedFormula.Realize (M := R) φ f (Fin.snoc k x)) := by simp  

def closed_under_function_formula {n} (χ : L.BoundedFormula α 1) (f : Functions L n) : L.Formula α :=
  relativize χ (Term.bdEqual (&(n : Fin (n+1))) (func f fun i => &i)).ex.alls


@[simp] lemma realize_closed_under_function_iff₀ (χ : L.BoundedFormula α 1) (f : Functions L 0) (k : _):
  Formula.Realize (M := R) (closed_under_function_formula χ f) k ↔ 
  BoundedFormula.Realize χ k (λ _ ↦ funMap f default) := by
  rw[closed_under_function_formula, alls, Formula.Realize]
  rw[relativize_ex]
  simp only [relativize, Nat.cast_zero, Function.comp_apply, Fin.coe_eq_castSucc, realize_ex, realize_inf, liftAt_snoc]
  constructor
  · rintro ⟨a,r,h⟩
    simp only [Realize, Fin.snoc, Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, cast_eq, dite_false,
      Term.realize_var, Sum.elim_inr, Term.realize_func] at h 
    rw[h] at r
    convert r
  · rintro h
    use funMap f default
    simp only [true_and, h]
    simp only [Realize, Fin.snoc, Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, cast_eq, dite_false,
      Term.realize_var, Sum.elim_inr, Term.realize_func]
    congr!

@[simp] lemma realize_closed_under_function_iff₁ (χ : L.BoundedFormula α 1) (f : Functions L 1) (k : _):
  Formula.Realize (M := R) (closed_under_function_formula χ f) k ↔ 
  (∀x,  BoundedFormula.Realize χ k x → BoundedFormula.Realize χ k (λ _ ↦ funMap f x)) := by
  rw[closed_under_function_formula, alls, Formula.Realize, alls, relativize]
  simp only [Nat.cast_one, Function.comp_apply, Fin.coe_fin_one, Nat.cast_zero, realize_all, realize_imp, liftAt_snoc,
    relativize_ex, realize_ex, realize_inf]
  constructor
  · rintro h x r
    have: x = λ _ ↦ x 0 := by ext a; let 0 := a; rfl
    rw[this] at r
    obtain ⟨a, fa, eq⟩ := h _ r
    simp only [Realize, Fin.snoc, Nat.lt_one_iff, Fin.castSucc_castLT, Fin.coe_fin_one, lt_self_iff_false,
      Fin.coe_castLT, cast_eq, dite_false, dite_eq_ite, Term.realize_var, Sum.elim_inr, ite_false, Term.realize_func,
      ite_true] at eq 
    rw[eq, ← this] at fa
    exact fa
  · rintro h x r
    use funMap f (λ _ ↦ x)
    simp only [r, relativize, true_and]
    simp only [Realize, Fin.snoc, Nat.lt_one_iff, Fin.castSucc_castLT, Fin.coe_fin_one, lt_self_iff_false,
      Fin.coe_castLT, cast_eq, dite_false, dite_eq_ite, Term.realize_var, Sum.elim_inr, ite_false, Term.realize_func,
      ite_true, and_true]
    apply h _ r
    
@[simp] lemma realize_closed_under_function_iff₂ (χ : L.BoundedFormula α 1) (f : Functions L 2) (k : _):
  Formula.Realize (M := R) (closed_under_function_formula χ f) k ↔ 
  (∀x y, BoundedFormula.Realize χ k (λ _ ↦ x) → 
        BoundedFormula.Realize χ k (λ _ ↦ y) → BoundedFormula.Realize χ k (λ _ ↦ funMap f ![x,y])) := by
  rw[closed_under_function_formula, alls, Formula.Realize, alls, alls, relativize, relativize]
  simp only [Nat.cast_one, Function.comp_apply, Fin.coe_fin_one, Nat.cast_zero, realize_all, realize_imp, liftAt_snoc,
    relativize_ex, realize_ex, realize_inf]
  constructor  
  · intro h x y h1 h2
    obtain ⟨t, pt, h1⟩ := h x h1 y h2
    simp only [Realize, Fin.snoc, Fin.castSucc_castLT, Fin.coe_castLT, Nat.lt_one_iff, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, dite_false, dite_eq_ite, Nat.cast_ofNat, Term.realize_var, Sum.elim_inr, ite_false,
      Fin.coe_eq_castSucc, Term.realize_func, Fin.coe_castSucc, Fin.is_lt, ite_true] at h1 
    rw[h1] at pt
    convert pt with _ b
    fin_cases b <;> simp
  · intro h x hx y hy
    use funMap f ![x, y]
    specialize h x y hx hy
    simp only [h, relativize, Nat.cast_ofNat, Fin.coe_eq_castSucc, true_and]
    simp only [Realize, Fin.snoc, Fin.castSucc_castLT, Fin.coe_castLT, Nat.lt_one_iff, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, dite_false, dite_eq_ite, Term.realize_var, Sum.elim_inr, ite_false, Term.realize_func,
      Fin.coe_castSucc, Fin.is_lt, ite_true]
    congr! with i
    fin_cases i <;> simp

def relativization_substructure₂ (χ : L.BoundedFormula α 1) (hl : ∀ n, L.Functions n → n = 0 ∨ n = 1 ∨ n = 2) (k : _)
  (hc : Formula.Realize (M := R) (closed_under_function_formula χ f : L.Formula α) k) : 
  L.Substructure R where
  carrier := {x | BoundedFormula.Realize χ k (λ _ ↦ x)}
  fun_mem := by
    intro n f xs h
    specialize hl _ f
    rcases hl with hl|hl|hl
    · sorry
    


end BoundedFormula

section 
variable (T : L.Theory)

end