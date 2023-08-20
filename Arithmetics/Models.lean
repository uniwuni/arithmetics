import Arithmetics.Robinson
import Arithmetics.QBFormulas
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


lemma Fin.comp_snoc_dep {n} {α β : Fin (n + 1) → Type*}
  {f : ∀{x}, α x → β x} {g : (i : Fin n) → α (Fin.castSucc i)} {a : α (Fin.last n)}:
  Fin.snoc (fun x => f (g x)) (f a) = λ x ↦ f (Fin.snoc g a x) := by
    ext j
    by_cases h : j.val < n
    · simp [h, Fin.snoc, Fin.castSucc_castLT]
    · rw [Fin.eq_last_of_not_lt h]
      simp

lemma qb_complete {n} {Φ : arith.BoundedFormula α n} (h : FirstOrder.Language.BoundedFormula.IsQB Φ) (f : _) (k : _):
  BoundedFormula.Realize (M := ℕ) Φ f k ↔ BoundedFormula.Realize (M := R) Φ (λ x ↦ OfNat.ofNat (f x)) (λ x ↦ OfNat.ofNat (k x)) :=
  match h with
  | BoundedFormula.IsQB.of_isQF h => qf_complete h f k
  | BoundedFormula.IsQB.imp h1 h2 => by
    simp only [BoundedFormula.realize_imp]
    rw[qb_complete h1 f k, qb_complete h2 f k]
  | BoundedFormula.IsQB.bounded_forall t h₁ => by
    simp only [Function.comp_apply, BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h a le
      simp[Term.le, BoundedFormula.realize_rel, relMap_le, leSymb] at le
      have : (Fin.last n : Fin (n + 1)) = ↑ n := by
        rw[Fin.eq_iff_veq, Fin.last]
        simp only [Fin.coe_ofNat_eq_mod]
        symm
        apply Nat.mod_eq_of_lt
        linarith
      rw[← this, Fin.snoc_last] at le
      unfold Function.comp at le
      let rec lem (t : arith.Term _): ∃n, Term.realize
        (fun x =>
          Sum.elim (fun x => OfNat.ofNat (f x)) (Fin.snoc (fun x => OfNat.ofNat (k x)) a) (Sum.map id Fin.castSucc x))
        t = (OfNat.ofNat n : R) :=
          (match t with
          | var v => by
              rcases v with a2|f2
              · simp
              · simp
          | func arithFunc.add ts => by
              simp only [Term.realize_func, funMap_add]
              obtain ⟨n1,a1⟩ := lem (ts 0)
              obtain ⟨n2,a2⟩ := lem (ts 1)
              rw[a1,a2, ← ofNat_add]
              use n1 + n2
          | func arithFunc.mul ts => by
              simp only [Term.realize_func, funMap_mul]
              obtain ⟨n1,a1⟩ := lem (ts 0)
              obtain ⟨n2,a2⟩ := lem (ts 1)
              rw[a1,a2, ← ofNat_mul]
              use n1 * n2
          | func arithFunc.zero ts => by
              simp only [Term.realize_func, funMap_zero]
              use 0
          | func arithFunc.one ts => by
              simp only [Term.realize_func, funMap_one]
              use 1
              rw[ofNat_one]
              unfold OfNat.ofNat instOfNat instOfNatNat
              simp only [ofNat', realize_succ, realize_zero, succ_zero_eq_one]
              rw[ofNat_one]
              )
      obtain ⟨n2, eq⟩ := lem t
      rw[eq, le_ofNat_iff] at le
      obtain ⟨m, le, eqm⟩ := le
      have h3 := qb_complete h₁
      rw[eqm]
      have a4 : (Fin.snoc (fun x => OfNat.ofNat (k x)) (OfNat.ofNat m)) = _ :=
        Fin.comp_snoc_dep (β := λ _ ↦ R) (α := λ _ ↦ ℕ) (f := λ a ↦ (OfNat.ofNat a : R)) (g := k)
      rw[a4]
      rw[← h3 _ _]
      apply h
      rw[← this]
      simp only [Term.le, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr, Fin.snoc_last,
        Term.realize_relabel]
      simp[leSymb, isOrderedArith]
      rw[← ofNat_le_ofNat (R := R)]
      rw[← ofNat_le_ofNat (R := R)] at le
      rw[← eq] at le
      convert le
      rw[← reduce_term]
      congr
      simp[Sum.elim_map]
      ext z
      rcases z with z|z
      · simp
      · simp
    · intro h a asm
      specialize h (OfNat.ofNat a)
      have h3 : BoundedFormula.Realize (Term.le (var (Sum.inr ↑n)) (Term.relabel (Sum.map id Fin.castSucc) t)) (fun x => OfNat.ofNat (f x)) (Fin.snoc (fun x => (OfNat.ofNat (k x) : R)) (OfNat.ofNat a)) := by
        rw[Fin.comp_snoc_dep (β := λ _ ↦ R) (α := λ _ ↦ ℕ) (f := λ a ↦ (OfNat.ofNat a : R)) (g := k)]
        rw[← qf_complete (R := R)]
        · apply asm
        · apply BoundedFormula.IsQF.of_isAtomic
          apply BoundedFormula.IsAtomic.rel

      have h5 := h h3
      rw[Fin.comp_snoc_dep (β := λ _ ↦ R) (α := λ _ ↦ ℕ) (f := λ a ↦ (OfNat.ofNat a : R)) (g := k)] at h5
      have h6 := (qb_complete h₁ (fun x => f x) (Fin.snoc (fun x => k x) a)).mpr h5
      exact h6

lemma exists_complete {Φ : arith.BoundedFormula Empty 1} (h : FirstOrder.Language.BoundedFormula.IsQB Φ) :
  BoundedFormula.Realize (M := ℕ) Φ.ex default default → BoundedFormula.Realize (M := R) Φ.ex default default := by
  rw[BoundedFormula.realize_ex, BoundedFormula.realize_ex]  
  rintro ⟨x, hx⟩
  use OfNat.ofNat x
  have hx2 := hx
  rw[qb_complete (R := R) h] at hx
  have h2 := (qb_complete (R := R) h default (λ _ ↦ x)).mp
  convert_to BoundedFormula.Realize (M := R) Φ (fun x => OfNat.ofNat ((default : Empty → ℕ) x)) fun _ => OfNat.ofNat x using 1
  apply h2
  convert hx2


end
end Arith.Robinson

end FirstOrder
