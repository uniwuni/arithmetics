import Arithmetics.Robinson

variable {α : Type*}
set_option autoImplicit false
namespace FirstOrder
namespace Arith
open Language.Theory

instance natCompatibleOrderedSemiring : CompatibleOrderedSemiring ℕ :=
  compatibleOrderedSemiringOfOrderedSemiring ℕ

theorem nat_models_robinson :
  ℕ ⊨ robinson_arithmetic := by
  simp only [robinson_arithmetic, Set.mem_insert_iff, Set.mem_singleton_iff, model_iff, forall_eq_or_imp, forall_eq]
  split_ands
  · unfold axiom_succ_ne_zero
    intro _
    simp
  · unfold axiom_succ_inj
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
    have: x ≤ y ↔ ∃ a, x + a = y := by
      simp[le_iff_exists_add]
      exact exists_congr (λ _ ↦ eq_comm)
    simp[this, Fin.snoc]


end Arith

end FirstOrder
