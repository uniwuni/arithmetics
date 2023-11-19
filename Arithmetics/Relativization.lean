import Arithmetics.QBFormulas
import Mathlib.ModelTheory.Substructures
import Mathlib.Tactic.FinCases

lemma Fin.append_snoc {m} (k1 : Fin n → α) (k2 : Fin m → α) (b : α) :
  (Fin.snoc (Fin.append k1 k2) b) = Fin.append k1 (Fin.snoc k2 b) := by
  have h: b = ![b] 0 := by simp
  rw[h, ← Fin.append_right_eq_snoc]
  rw[Fin.append_assoc]
  ext x
  simp
  rw[Fin.append_right_eq_snoc]
  congr

lemma Fin.one_is_const (x : Fin 1 → α) : x = (λ _ ↦ x 0) := by ext x; let 0 := x; simp

@[simp] lemma Fin.snoc_one_of_zero : (Fin.snoc default m : Fin 1 → α) i = m := by
  let 0 := i
  simp[snoc]

lemma Fin.natAdd_eq_last : ((Fin.natAdd n 0) : Fin (n+1)) = Fin.last n  := by 
          apply Fin.eq_of_val_eq
          simp 

@[simp] lemma Fin.cast_eq_last {n : ℕ} : ↑n = Fin.last n := by
  apply Fin.eq_of_val_eq
  simp

namespace FirstOrder.Language

class AtMostBinaryFunctions (L : Language) where
  at_most_binary : ∀ n, L.Functions n → n ≤ 2

open FirstOrder.Language
open FirstOrder
open Language Structure 
variable {L : Language} {n : ℕ} {α : Type*}

namespace Term

def liftAt' {n : ℕ} (n' : ℕ) : L.Term (Sum α (Fin n)) → L.Term (Sum α (Fin (n' + n))) :=
  relabel (Sum.map id fun i => Fin.natAdd n' i)
end Term


namespace BoundedFormula
variable (χ : L.Formula (α ⊕ Fin 1))
def relativize : {n : ℕ} → L.BoundedFormula α n → L.BoundedFormula α n
| _, falsum => falsum
| _, imp φ ψ => imp (relativize φ) (relativize ψ)
| _, rel r xs => rel r xs
| _, equal a b => equal a b
| n, all φ => all (BoundedFormula.relabel (Sum.map id (λ _ ↦ (n : Fin (n+1)))) χ ⟹ (relativize φ))

lemma qb_of_imp {φ ψ : L.BoundedFormula α n} (hqf : IsQF (φ.imp ψ)) : IsQF φ ∧ IsQF ψ := by
  match hqf with
  | IsQF.imp h₁ h₂ => exact ⟨h₁, h₂⟩

@[simp] lemma relativize_of_qf {φ : L.BoundedFormula α n} (hqf : IsQF φ) : relativize χ φ = φ := by
  induction hqf with
  | falsum => rfl
  | imp qf1 qf2 pφ pψ => simp only [relativize, imp.injEq]; tauto
  | of_isAtomic a => rcases a; simp[relativize, Term.bdEqual]; simp[relativize, Relations.boundedFormula]
end BoundedFormula
section
variable {R : Type*} [Structure L R] 
namespace Formula
lemma realize_iff_models (φ : L.Formula Empty) (k : Empty → R) :
  Formula.Realize φ k ↔ R ⊨ φ := by
  rw[Sentence.Realize]
  congr!
end Formula
namespace BoundedFormula
lemma realize_iff_formula_realize (φ : L.Formula α) (k : α → R) (l : Fin 0 → R) :
  BoundedFormula.Realize φ k l ↔ Formula.Realize φ k := by
  simp only [Formula.Realize]
  have : l = default := by ext x; fin_cases x
  rw[this]
@[simp] lemma realize_falsum {n} (f : α → R) (k : Fin n → R) : Realize (L := L) (M := R) falsum f k ↔ False := by rfl
/-
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
-/
variable (χ : L.Formula (α ⊕ Fin 1))
lemma relativize_ex' {φ : L.BoundedFormula α (n + 1)} (f : _) (k : _) :
  BoundedFormula.Realize (M := R) ((relativize χ φ.ex) ⇔ (BoundedFormula.relabel (Sum.map id (λ _ ↦ (n : Fin (n+1)))) χ ⊓ relativize χ φ).ex) f k := by
  rw[BoundedFormula.ex]
  simp only [relativize, Nat.add_zero, realize_iff, realize_imp, realize_all, realize_relabel, Fin.castAdd_zero,
    Fin.cast_refl, Function.comp.right_id, realize_falsum, realize_ex, realize_inf]
  rw[← not_exists_not]
  simp

@[simp]
lemma relativize_ex {φ : L.BoundedFormula α (n + 1)}  (f : _) (k : _) :
  BoundedFormula.Realize (M := R) (relativize χ φ.ex) f k ↔ BoundedFormula.Realize (M := R) (BoundedFormula.relabel (Sum.map id (λ _ ↦ (n : Fin (n+1)))) χ ⊓ relativize χ φ).ex f k := by
  rw[BoundedFormula.ex]
  simp only [relativize, Nat.add_zero, realize_iff, realize_imp, realize_all, realize_relabel, Fin.castAdd_zero,
    Fin.cast_refl, Function.comp.right_id, realize_falsum, realize_ex, realize_inf]
  rw[← not_exists_not]
  simp

@[simp]
lemma relativize_ex_aux {φ : L.BoundedFormula α (n + 1)} (f : _) (k : _) :
  BoundedFormula.Realize (M := R) (BoundedFormula.relabel (Sum.map id (λ _ ↦ (n : Fin (n+1)))) χ ⊓ relativize χ φ).ex f k
    ↔ (∃ x, Formula.Realize (M := R) χ (Sum.elim f (λ _ ↦ x))  ∧ BoundedFormula.Realize (M := R) (relativize χ φ) f (Fin.snoc k x)) := by
  simp only [Nat.add_zero, realize_ex, realize_inf, realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp.right_id, Formula.Realize]  
  apply exists_congr
  simp
  intro a _
  congr!
  ext x
  rcases x with x|x
  · simp
  · fin_cases x
    simp

def closed_under_function_formula {n} (f : Functions L n) : L.Formula α :=
  relativize χ (Term.bdEqual (&(n : Fin (n+1))) (func f fun i => &i)).ex.alls


class ClosedUnderFunctions (k : _) where
  isClosedUnderFunctions : ∀n, ∀ f : L.Functions n, Formula.Realize (M := R) (closed_under_function_formula χ f : L.Formula α) k

@[simp] lemma realize_closed_under_function_iff₀ (f : Functions L 0) (k : _):
  Formula.Realize (M := R) (closed_under_function_formula χ f) k ↔ 
  Formula.Realize χ (Sum.elim k (λ _ ↦ funMap f default)) := by
  rw[closed_under_function_formula, alls, Formula.Realize]
  rw[relativize_ex]
  simp only [Nat.add_zero, Nat.cast_zero, relativize, Function.comp_apply, Fin.coe_eq_castSucc, realize_ex, Fin.snoc,
    Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, cast_eq, dite_false, realize_inf, realize_relabel,
    Fin.castAdd_zero, Fin.cast_refl, Function.comp.right_id]
  constructor 
  · rintro ⟨a, ha1, ha2⟩
    have : ((fun _ => a) ∘ Fin.natAdd (0 + 1)) = (default : Fin 0 → R) := by ext x; fin_cases x
    rw[this, ← Formula.Realize] at ha1
    simp only [Realize, Term.realize_var, Sum.elim_inr, Term.realize_func] at ha2 
    convert ha1
    ext x
    rcases x with x|x
    · simp
    · simp only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]
      rw[ha2]
      congr
      apply Subsingleton.allEq
  · rintro h
    use funMap f default
    have : (fun i => funMap f default) ∘ Fin.natAdd (0 + 1) = (default : Fin 0 → R) := by ext x; fin_cases x
    rw[this, ← Formula.Realize]
    constructor
    · convert h using 1
      ext x
      rcases x with x|_
      · simp
      · simp
    · simp only [Realize, Term.realize_var, Sum.elim_inr, Term.realize_func]
      congr!
     


@[simp] lemma realize_closed_under_function_iff₁ (f : Functions L 1) (k : _):
  Formula.Realize (M := R) (closed_under_function_formula χ f) k ↔ 
  (∀x,  Formula.Realize χ (Sum.elim k x) → Formula.Realize χ (Sum.elim k (λ _ ↦ funMap f x))) := by
  rw[closed_under_function_formula, alls, Formula.Realize, alls]
  simp only [relativize, Nat.cast_zero, zero_add, Nat.cast_one, Function.comp_apply, Fin.coe_fin_one, realize_all,
    realize_imp, realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp.right_id, realize_falsum]
  simp only [Formula.Realize._eq_1]
  constructor
  · rintro h x r
    have: x = λ _ ↦ x 0 := by ext a; let 0 := a; rfl
    rw[this] at r
    have : (Sum.elim k (Fin.snoc (default : Fin 0 → _)  (x 0)) ∘ Sum.map id fun _ => 0) = (Sum.elim k (fun _ ↦ x 0) : α ⊕ Fin 1 → R) := by
      ext (i|_)
      · simp
      · simp only [Function.comp_apply, Sum.map_inr, Sum.elim_inr, Fin.snoc_one_of_zero]
    specialize h (x 0) (by rw[← this] at r; convert r) 
    rw[← not_exists_not] at h
    simp only [realize_iff_formula_realize, exists_prop, and_true, not_forall] at h 
    rcases h with ⟨y,hy1,hy2⟩ 
    simp only [Fin.snoc, Nat.lt_one_iff, Fin.castSucc_castLT, Fin.coe_fin_one, lt_self_iff_false, Fin.coe_castLT,
      cast_eq, dite_false, dite_eq_ite, Formula.Realize._eq_1, Realize, Term.realize_var, Sum.elim_inr, ite_false,
      Term.realize_func, ite_true] at hy1 hy2 
    rw[hy2, Sum.elim_comp_map] at hy1
    convert hy1 with a
    let 0 := a
    simp only [Function.comp_apply, ite_false]
    rw[Fin.one_is_const x]
  · rintro h x r
    rw[← not_exists_not]
    simp only [exists_prop, and_true, not_forall]
    use funMap f (λ _ ↦ x)
    constructor
    · rw[Sum.elim_comp_map]
      rw[Sum.elim_comp_map] at r
      specialize h (λ _ ↦ x)
      have : Realize χ (Sum.elim k fun _ => x) default := by convert r
      specialize h this
      convert h
            
    · simp[Realize, Fin.snoc] 
    
@[simp] lemma realize_closed_under_function_iff₂ (f : Functions L 2) (k : _):
  Formula.Realize (M := R) (closed_under_function_formula χ f) k ↔ 
  (∀x y,  Formula.Realize χ (Sum.elim k (λ_ ↦ x)) → 
        Formula.Realize χ (Sum.elim k (λ _ ↦ y)) → Formula.Realize χ (Sum.elim k (λ _ ↦ funMap (M := R) f ![x,y]))) := by
  rw[closed_under_function_formula, alls, Formula.Realize, alls, alls]
  simp only [relativize, Nat.cast_zero, zero_add, Nat.cast_one, Nat.cast_add, Nat.cast_ofNat, Function.comp_apply,
    Fin.coe_eq_castSucc, realize_all, realize_imp, realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp.right_id, realize_falsum]
  simp only [Formula.Realize._eq_1]
  constructor
  · intro h x y rx ry
    specialize h x _ y _
    · convert rx
      ext (x|_)
      · simp
      · simp
    · convert ry
      ext (x|x)
      · simp
      · simp[Fin.snoc]
    rw[← not_exists_not] at h
    simp only [exists_prop, and_true, not_forall] at h 
    rcases h with ⟨z, h1z, h2z⟩
    simp only [Realize, Fin.snoc, Fin.castSucc_castLT, Fin.coe_castLT, Nat.lt_one_iff, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, dite_false, dite_eq_ite, Term.realize_var, Sum.elim_inr, ite_false, Term.realize_func,
      Fin.coe_castSucc, Fin.is_lt, ite_true] at h2z
    simp only [h2z] at h1z
    convert h1z
    ext x
    rcases x with x|z
    · simp
    · simp only [Sum.elim_inr, Fin.snoc, Fin.castSucc_castLT, Fin.coe_castLT, Nat.lt_one_iff, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, dite_false, dite_eq_ite, Function.comp_apply, Sum.map_inr, ite_false]
      congr
      ext i
      fin_cases i <;> simp
  · intro h x rx y ry 
    rw[← not_exists_not]
    simp only [exists_prop, and_true, not_forall]
    use funMap (M := R) f ![x,y]
    constructor
    · convert h x y _ _
      · ext (i|i)
        · simp
        · simp[Fin.snoc]
      · convert rx
        ext (i|i)
        · simp
        · simp[Fin.snoc]
      · convert ry
        ext (i|i)
        · simp
        · simp[Fin.snoc]
    · simp only [Realize, Fin.snoc, Fin.castSucc_castLT, Fin.coe_castLT, Nat.lt_one_iff, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, dite_false, dite_eq_ite, Term.realize_var, Sum.elim_inr, ite_false, Term.realize_func,
      Fin.coe_castSucc, Fin.is_lt, ite_true]
      congr
      ext i
      fin_cases i <;> simp

def RelativizationSubstructure₂' [AtMostBinaryFunctions L] (k : α → R)
  [ClosedUnderFunctions (R := R) χ k] : 
  L.Substructure R where
  carrier := {x | Formula.Realize χ (Sum.elim k (λ _ ↦ x))}
  fun_mem := by
    have hc := ClosedUnderFunctions.isClosedUnderFunctions (χ := χ) (k := k)
    intro m f xs h
    have hl := AtMostBinaryFunctions.at_most_binary _ f
    match m with
    | 0 =>
      simp only [Set.mem_setOf_eq]
      specialize hc 0 f
      rw[realize_closed_under_function_iff₀] at hc
      convert hc
    | 1 =>
      simp only [Set.mem_setOf_eq]
      specialize hc 1 f
      rw[realize_closed_under_function_iff₁] at hc
      apply hc
      specialize h 0
      simp only [Set.mem_setOf_eq] at h
      convert h
    | 2 => 
      simp only [Set.mem_setOf_eq]
      specialize hc 2 f
      rw[realize_closed_under_function_iff₂] at hc
      specialize hc (xs 0) (xs 1)
      have h0 := h 0
      have h1 := h 1
      simp only [Set.mem_setOf_eq] at h0 h1
      convert hc h0 h1
      ext i
      fin_cases i <;> simp
    | n + 3 => 
      linarith[hl]


def RelativizationSubstructure₂ (χ : L.Formula (Empty ⊕ Fin 1)) [AtMostBinaryFunctions L]
  [ClosedUnderFunctions (R := R) χ k] : L.Substructure R := RelativizationSubstructure₂' χ k

section
variable (k : α → R)  (χ : L.Formula (α ⊕ Fin 1)) [AtMostBinaryFunctions L] [ClosedUnderFunctions (R := R) χ (k := k)]

@[simp] lemma relativizationSubstructure₂'_mem (x : R) :
    x ∈ RelativizationSubstructure₂' χ k ↔ Formula.Realize χ (Sum.elim k (λ _ ↦ x)) := by
  simp only [RelativizationSubstructure₂']
  simp_rw[← Substructure.mem_carrier, Set.mem_setOf_eq]

--@[simp] lemma relativizationSubstructure₂_mem (x : R) :
--    x ∈ RelativizationSubstructure₂ (R := R) χ ↔ Formula.Realize χ (λ _ ↦ x) := by
--  simp only [RelativizationSubstructure₂]
--  simp

@[simp] lemma relativizationSubstructure₂'_realizes_iff {n : ℕ} (φ : L.BoundedFormula α n)
  (v : Fin n → RelativizationSubstructure₂' (R := R) χ k) (k_in : ∀i, k i ∈ RelativizationSubstructure₂' (R := R) χ k):
  BoundedFormula.Realize (M := RelativizationSubstructure₂' (R := R) χ k) φ 
    (λ i ↦ ⟨k i, k_in i⟩) v ↔ 
  BoundedFormula.Realize (M := R) (relativize χ φ) k (((↑) ∘ v) : Fin n → R) := by induction φ with
    | falsum => simp[relativize]
    | imp φ ψ pφ pψ =>
      simp only [realize_imp, relativize]
      apply imp_congr
      · apply pφ
      · apply pψ
    | rel r xs =>
      rw[relativize, Realize, Realize, RelMap]
      simp only [Substructure.inducedStructure]
      conv =>
        lhs
        arg 2
        ext
        rw[← realize_term_substructure]
        arg 1
        rw[Sum.comp_elim]
    | equal x y =>
      rw[relativize, Realize, Realize]
      simp only [Substructure.inducedStructure]
      rw[Subtype.ext_iff]
      rw[← realize_term_substructure, ← realize_term_substructure]
      rw[Sum.comp_elim]
      congr!
    | all φ pφ =>
      rw[relativize, Realize, Realize]
      simp
      apply forall_congr'
      intro x
      constructor
      · intro h is_χ
        specialize h _
        · rw[relativizationSubstructure₂'_mem, Formula.Realize]
          convert is_χ with ⟨a|a⟩
          · rw[Sum.elim_comp_map]
            congr! with a
            let 0 := a
            simp
        · rw[pφ] at h
          convert h
          rw[Fin.comp_snoc]
      · intro h prf
        specialize h _
        · rw[relativizationSubstructure₂'_mem, Formula.Realize] at prf
          convert prf with ⟨a|a⟩
          · rw[Sum.elim_comp_map]
            congr! with a
            let 0 := a
            simp
        · rw[pφ (Fin.snoc v ({ val := x, property := prf } :  { a // a ∈ RelativizationSubstructure₂' χ k }))]
          convert h
          rw[Fin.comp_snoc]


@[simp]
lemma relativizationSubstructure₂_qf_iff {φ : L.BoundedFormula α n} (hqf : IsQF φ) 
  {xs : Fin n → RelativizationSubstructure₂' (R := R) χ k} (k_in : ∀i, k i ∈ RelativizationSubstructure₂' (R := R) χ k) :
    φ.Realize (λ i ↦ ⟨k i, k_in i⟩) xs ↔ φ.Realize (M := R) k (((↑) ∘ xs) : Fin n → R) := 
  match hqf with
  | IsQF.falsum => by rfl
  | IsQF.of_isAtomic (IsAtomic.rel r ts) => by
    rw[relativizationSubstructure₂'_realizes_iff]
    simp only [relativize, realize_rel, Realize]
  | IsQF.of_isAtomic (IsAtomic.equal a b) => by
    rw[relativizationSubstructure₂'_realizes_iff]
    simp only [relativize, realize_bdEqual, Realize]
  | IsQF.imp h₁ h₂ => by
    simp only [realize_imp]
    rw[relativizationSubstructure₂_qf_iff h₁, relativizationSubstructure₂_qf_iff h₂]


lemma relativizationSubstructure_universal_of {φ : L.BoundedFormula α n} (hqf : IsQF φ) 
   (k_in : ∀i, k i ∈ RelativizationSubstructure₂' (R := R) χ k) :
    (φ.alls).Realize (M := R) k → φ.alls.Realize (M := RelativizationSubstructure₂' (R := R) χ k) (λ i ↦ ⟨k i, k_in i⟩) := by
  intro h
  rw[realize_alls]
  rw[realize_alls] at h
  intro xs
  simp only [relativizationSubstructure₂'_realizes_iff]
  rw[relativize_of_qf]
  apply h
  apply hqf

lemma relativizationSubstructure_universal_one {φ : L.BoundedFormula α _} (hqf : IsQF φ) 
  {xs : Fin n → RelativizationSubstructure₂' (R := R) χ k}  (k_in : ∀i, k i ∈ RelativizationSubstructure₂' (R := R) χ k) :
    φ.all.Realize (M := R) k (((↑) ∘ xs) : Fin n → R) → φ.all.Realize (M := RelativizationSubstructure₂' (R := R) χ k) (λ i ↦ ⟨k i, k_in i⟩) xs := by
  intro h
  rw[realize_all]
  rw[realize_all] at h
  intro ys
  simp only [relativizationSubstructure₂'_realizes_iff]
  rw[relativize_of_qf]
  convert h ys
  rw[Fin.comp_snoc]
  · exact hqf

end
end BoundedFormula

section 
variable (T : L.Theory)

end