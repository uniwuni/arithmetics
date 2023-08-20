import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Satisfiability
namespace FirstOrder.Language

open FirstOrder
variable {L} [IsOrdered L] {n : ℕ} {T : Theory L}
--variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Fin l → M}
namespace BoundedFormula
/-- Formulas where all quantifiers are bounded. These are not all such formulas,
    but all equivalence classes are hit.
-/
inductive IsQB : {n : ℕ} → L.BoundedFormula α n → Prop
  | of_isQF {φ} (h₁ : φ.IsQF) : IsQB φ
  | imp {n} {φ₁ φ₂} (h₁ : IsQB (n := n) φ₁) (h₂ : IsQB φ₂) : IsQB (φ₁.imp φ₂)
  | bounded_forall {n} {φ₁} (t : L.Term (α ⊕ Fin n)) (h₁ : IsQB (n := n + 1) φ₁) : IsQB (∀' ((&(↑ n)).le (t.relabel (Sum.map id Fin.castSucc)) ⟹ φ₁))

theorem IsQF.isQB {φ : L.BoundedFormula α n} : φ.IsQF → φ.IsQB :=
  IsQB.of_isQF

theorem IsAtomic.isQB {φ : L.BoundedFormula α n} : φ.IsAtomic → φ.IsQB :=
  IsQB.of_isQF ∘ IsQF.of_isAtomic

theorem isQB_bot : IsQB (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum.isQB

theorem IsQB.not {φ : L.BoundedFormula α n} (h : IsQB φ) : IsQB φ.not :=
  h.imp isQB_bot


variable (T : Theory L)
open Theory
structure QBEquiv (φ : L.BoundedFormula α n) :=
  formula : L.BoundedFormula α n
  isQB : IsQB formula
  equiv : T.SemanticallyEquivalent φ formula

theorem IsQB.isQBEquiv {φ : L.BoundedFormula α n} (h : IsQB φ) : QBEquiv T φ where
  formula := φ
  isQB := h
  equiv := refl _

section
variable {φ ψ : L.BoundedFormula α n} (hφ : QBEquiv T φ) (hψ : QBEquiv T ψ)

theorem QBEquiv.not : QBEquiv T φ.not where
  formula := hφ.formula.not
  isQB := hφ.isQB.not
  equiv := SemanticallyEquivalent.not hφ.equiv

@[simp]
lemma QBEquiv.not_formula : (QBEquiv.not T hφ).formula = hφ.formula.not := by
  rw[formula]
  unfold not
  simp


theorem QBEquiv.imp : QBEquiv T (φ.imp ψ) where
  formula := hφ.formula.imp hψ.formula
  isQB := hφ.isQB.imp hψ.isQB
  equiv := SemanticallyEquivalent.imp hφ.equiv hψ.equiv

@[simp]
lemma QBEquiv.imp_formula : (QBEquiv.imp T hφ hψ).formula = hφ.formula.imp hψ.formula := by
  rw[formula]
  unfold imp
  simp

theorem QBEquiv.or : QBEquiv T (φ ⊔ ψ) where
  formula := hφ.formula.not.imp hψ.formula
  isQB := hφ.isQB.not.imp hψ.isQB
  equiv := by 
    intro M v xs
    have h1 := hφ.equiv
    have h2 := hψ.equiv
    simp only [realize_iff, realize_sup, realize_imp, realize_not]
    have h3 := h1 M v xs
    have h4 := h2 M v xs
    simp only [realize_iff] at h3 h4
    rw[h3, h4]
    rw[or_iff_not_imp_left]

@[simp]
lemma QBEquiv.or_formula : (QBEquiv.or T hφ hψ).formula = hφ.formula.not.imp hψ.formula := by
  rw[formula]
  unfold or
  simp

theorem QBEquiv.and : QBEquiv T (φ ⊓ ψ) where
  formula := (((hφ.not T).or T (hψ.not T)).not T).formula
  isQB := (((hφ.not T).or T (hψ.not T)).not T).isQB
  equiv := by
    intro M v xs
    have h1 := hφ.equiv
    have h2 := hψ.equiv
    simp only [realize_iff, realize_inf]
    have h3 := h1 M v xs
    have h4 := h2 M v xs
    simp only [realize_iff] at h3 h4
    rw[h3, h4]
    simp
    
@[simp]
lemma QBEquiv.and_formula : (QBEquiv.and T hφ hψ).formula = (((hφ.not T).or T (hψ.not T)).not T).formula := by
  rw[formula]
  unfold and
  simp
end
section
variable {φ ψ : L.BoundedFormula α (n + 1)} (hφ : QBEquiv T φ) (hψ : QBEquiv T ψ)
lemma QBEquiv.bounded_forall (t : L.Term (α ⊕ Fin n)) : QBEquiv T (∀' ((&(↑ n)).le (t.relabel (Sum.map id Fin.castSucc)) ⟹ φ)) where
  formula := (∀' ((&(↑ n)).le (t.relabel (Sum.map id Fin.castSucc)) ⟹ hφ.formula))
  isQB := hφ.isQB.bounded_forall t
  equiv := by
    intro M v xs
    simp only [Function.comp_apply, realize_iff, realize_all, realize_imp]
    apply forall_congr'
    intro a
    have h1 := hφ.equiv
    have h3 := h1 M v (Fin.snoc xs a)
    simp only [realize_iff] at h3
    rw[h3]

lemma QBEquiv.bounded_exists (t : L.Term (α ⊕ Fin n)) : QBEquiv T (∃' ((&(↑ n)).le (t.relabel (Sum.map id Fin.castSucc)) ⊓ φ)) where
  formula := (∀' ((&(↑ n)).le (t.relabel (Sum.map id Fin.castSucc)) ⟹ hφ.formula.not)).not
  isQB := (hφ.isQB.not.bounded_forall t).not
  equiv := by
    intro M v xs
    simp only [Function.comp_apply, realize_iff, realize_all, realize_imp]
    unfold BoundedFormula.ex
    apply not_congr
    apply forall_congr'
    intro a
    have h1 := hφ.equiv
    have h3 := h1 M v (Fin.snoc xs a)
    simp only [realize_iff] at h3
    simp only [realize_not, realize_inf, not_and, realize_imp]
    rw[h3]




end
  /-


theorem IsQB.liftAt {φ : L.BoundedFormula α n} {k m : ℕ} (h : IsQB φ) : (φ.liftAt k m).IsQB :=
  match h with
    | of_isQF h₁ => (h₁.liftAt).isQB
    | imp h₁ h₂ => by
      unfold liftAt
      simp[mapTermRel]
      apply imp
      · exact IsQB.relabel h₁ f
      · exact IsQB.relabel h₂ f
    | bounded_forall t h₁ => by
      simp [Term.le]
      apply bounded_forall


theorem IsQF.castLE {h : l ≤ n} (hφ : IsQF φ) : (φ.castLE h).IsQF :=
  IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2



theorem IsQB.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQB) (f : α → Sum β (Fin n)) :
    (φ.relabel f).IsQB :=
    match h with
    | of_isQF h₁ => (h₁.relabel f).isQB
    | imp h₁ h₂ => by
      simp only [relabel_imp]
      apply imp
      · exact IsQB.relabel h₁ f
      · exact IsQB.relabel h₂ f

    | bounded_forall t h₁ => by
      simp [Term.le]
      apply bounded_forall

--/