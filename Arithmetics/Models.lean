import Arithmetics.Robinson

variable {α : Type*}
set_option autoImplicit false
namespace FirstOrder
namespace Arith.Robinson
open Language.Theory
open Language arith Structure 

theorem nat_models_robinson :
  ℕ ⊨ Q := by
  simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff, model_iff, forall_eq_or_imp, forall_eq]
  split_ands
  · unfold axiom_succ_ne_zero
    intro _
    simp
  · unfold axiom_succ_inj_of
    intro _
    simp
  · unfold axiom_add_zero
    intro _
    simp 
  · unfold axiom_add_succ
    intro _ _
    simp only [Function.comp_apply, Language.BoundedFormula.realize_bdEqual, realize_add, Language.Term.realize_var,
      Sum.elim_inr, realize_succ]
    rfl
  · unfold axiom_mul_zero
    intro _
    simp
  · unfold axiom_mul_succ
    intro _ _
    simp only [Function.comp_apply, Language.BoundedFormula.realize_bdEqual, realize_mul, Language.Term.realize_var,
      Sum.elim_inr, realize_succ, realize_add]
    rfl
  · unfold axiom_zero_or_succ
    intro x
    simp only [Function.comp_apply, Language.BoundedFormula.realize_sup, Language.BoundedFormula.realize_bdEqual,
      Language.Term.realize_var, Sum.elim_inr, realize_zero, Language.BoundedFormula.realize_ex, realize_succ]
    match x with
      | 0 => simp
      | n + 1 =>
        right
        use n
        simp[Fin.snoc]
  · unfold axiom_le_iff_ex_add
    intro x y
    have: x ≤ y ↔ ∃ a, a + x = y := by
      simp[le_iff_exists_add]
      exact exists_congr (λ _ ↦ by rw[eq_comm, add_comm])
    simp[this, Fin.snoc]
  · unfold axiom_succ_zero_eq_one
    rfl

section
variable {R : Type*} [Add R] [Mul R] [LE R] [One R] [Zero R] [CompatibleOrderedSemiring R]
variable [RobinsonStructure R]
open RobinsonStructure
open CompatibleOrderedSemiring

lemma reduce_term (t : arith.Term α) (k : α → ℕ) :
  Term.realize (M := R) (λ x ↦ OfNat.ofNat (k x)) t = OfNat.ofNat (Term.realize (M := ℕ) k t) := 
  match t with
  | var v => by simp
  | func arithFunc.add ts => by
    simp only [Term.realize_func, funMap_add]
    rw[funMap_add, ofNat_add]
    congr
    · apply reduce_term (ts 0)
    · apply reduce_term (ts 1)
  | func arithFunc.mul ts => by
    simp only [Term.realize_func, funMap_mul]
    rw[funMap_mul, ofNat_mul]
    congr
    · apply reduce_term (ts 0)
    · apply reduce_term (ts 1)
  | func arithFunc.zero ts => by
    simp only [Term.realize_func, funMap_zero]
    rw[funMap_zero]
    rfl
  | func arithFunc.one ts => by
    simp only [Term.realize_func, funMap_one]
    rw[funMap_one, ←succ_zero_eq_one]
    rfl

lemma qf_complete {n} {Φ : arith.BoundedFormula α n} (h : FirstOrder.Language.BoundedFormula.IsQF Φ) (f : _) (k : _):
  BoundedFormula.Realize (M := ℕ) Φ f k ↔ BoundedFormula.Realize (M := R) Φ (λ x ↦ OfNat.ofNat (f x)) (λ x ↦ OfNat.ofNat (k x)) := by
  induction h with
  | falsum => 
    constructor
    · intro h2
      exfalso
      exact h2
    · intro h2
      exfalso
      exact h2
  | of_isAtomic h => 
    cases h with
    | equal t1 t2 =>
      constructor
      · intro h
        simp only [BoundedFormula.realize_bdEqual]
        have:
          (Sum.elim (fun x => OfNat.ofNat (α := R) (f x)) fun x => OfNat.ofNat (k x)) = 
            (λ a ↦ OfNat.ofNat (Sum.elim f k a)) := by
          ext x
          rcases x with x|x
          · simp  
          · simp
        
        rw[this, reduce_term, reduce_term]
        rw[h]
      · intro h 
        simp only [BoundedFormula.realize_bdEqual]
        simp only [BoundedFormula.realize_bdEqual] at h
        have:
          (Sum.elim (fun x => OfNat.ofNat (α := R) (f x)) fun x => OfNat.ofNat (k x)) = 
            (λ a ↦ OfNat.ofNat (Sum.elim f k a)) := by
          ext x
          rcases x with x|x
          · simp  
          · simp
        rw[this] at h
        rw[reduce_term, reduce_term] at h
        rw[← ofNat_inj (R := R)]
        exact h
    | @rel l rel ts =>
      let 2 := l
      rcases rel with ⟨⟩
      constructor
      · intro h
        simp only [BoundedFormula.realize_rel, relMap_le]
        have:
          (Sum.elim (fun x => OfNat.ofNat (α := R) (f x)) fun x => OfNat.ofNat (k x)) = 
            (λ a ↦ OfNat.ofNat (Sum.elim f k a)) := by
          ext x
          rcases x with x|x
          · simp  
          · simp
        
        rw[this, reduce_term, reduce_term]
        rw[ofNat_le_ofNat]
        exact h
      · intro h 
        simp only [BoundedFormula.realize_rel, relMap_le]
        simp only [BoundedFormula.realize_rel, relMap_le] at h 
        have:
          (Sum.elim (fun x => OfNat.ofNat (α := R) (f x)) fun x => OfNat.ofNat (k x)) = 
            (λ a ↦ OfNat.ofNat (Sum.elim f k a)) := by
          ext x
          rcases x with x|x
          · simp  
          · simp
        rw[this] at h
        rw[reduce_term, reduce_term] at h
        rw[← ofNat_le_ofNat (R := R)]
        exact h
  | imp _ _ ih1 ih2 => simp[*]



end Arith

end FirstOrder
