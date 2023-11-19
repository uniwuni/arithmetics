import Arithmetics.RobinsonModels
import Arithmetics.Relativization

instance : FirstOrder.Language.AtMostBinaryFunctions FirstOrder.Language.arith where
  at_most_binary n f := by
    rcases f <;> simp

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

local instance rModels : R ⊨ Q := by rw[satisfies_robinson_iff]; infer_instance

variable (S : Substructure arith R) (closed_pred : ∀ x, x + 1 ∈ S → x ∈ S)
  (closed_le : ∀ x y, x + y ∈ S → y ∈ S → x ∈ S)

instance substructureModelsRobinson : S ⊨ Q where
  realize_of_mem := by
    intro ψ ψ_in
    rcases ψ_in with h|(h|(h|(h|(h|(h|(h|(h|h)))))))
    · rw[h]
      simp only [axiom_succ_ne_zero, succ, Function.comp_apply]
      intro x
      simp[Term.realize, funMap, Fin.snoc, Matrix.vecCons]
    · rw[h]
      simp only [axiom_succ_inj_of, succ, Function.comp_apply]
      intro x
      simp[Term.realize, Fin.snoc, Matrix.vecCons, funMap]
    · rw[h]
      simp only [axiom_add_zero, Function.comp_apply]
      intro x
      simp[Term.realize, Fin.snoc, Matrix.vecCons, funMap]
    · rw[h]
      simp only [axiom_add_succ, Function.comp_apply, succ]
      intro x
      simp[Term.realize, Fin.snoc, Matrix.vecCons, funMap]
    · rw[h]
      simp only [axiom_mul_zero, Function.comp_apply]
      intro x
      simp[Term.realize, Fin.snoc, Matrix.vecCons, funMap]
    · rw[h]
      simp only [axiom_mul_succ, Function.comp_apply, succ]
      intro x
      simp[Term.realize, Fin.snoc, Matrix.vecCons, funMap]
    · rw[h]
      simp only [axiom_zero_or_succ, Function.comp_apply, succ]
      intro x
      simp only [Fin.snoc, Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, cast_eq, dite_false,
        BoundedFormula.realize_sup, BoundedFormula.realize_bdEqual, Term.realize, Sum.elim_inr,
        BoundedFormula.realize_ex, zero_add, Nat.lt_one_iff, dite_eq_ite, ite_true, ite_false, Subtype.exists]   
      rcases zero_or_succ x.val with (⟨eq⟩|⟨x2, eq⟩)
      · left
        apply Subtype.eq
        rw[eq]
        simp[funMap]
      · right
        use x2
        have := x.property
        rw[eq] at this
        use closed_pred x2 this
        apply Subtype.eq
        simp only [eq, Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, ite_false, Matrix.cons_val_one,
          Matrix.head_cons]
        congr
    · rw[h]
      simp only [axiom_le_iff_ex_add, leRel, Function.comp_apply]
      intro x y
      -- simp? doesnt work here for some reason
      simp[Term.realize, Fin.snoc, Matrix.vecCons, RelMap, funMap, arithRel.le]
      rw[← Subtype.coe_le_coe]
      rw[le_iff_ex_add]
      apply exists_congr
      intro a
      constructor
      · intro h
        specialize closed_le a (↑ x)
        rw[h] at closed_le
        specialize closed_le y.prop x.prop
        use closed_le
        simp[h]
      · rintro ⟨h, prop⟩
        rw[Subtype.ext_iff] at prop
        simp only at prop 
        exact prop
    · rw[h]
      simp only [Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Term.realize, succ_zero_eq_one, Matrix.vecCons, funMap]
      
