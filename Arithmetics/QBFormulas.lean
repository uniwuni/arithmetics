import Mathlib.ModelTheory.Order
namespace FirstOrder.Language

open FirstOrder
variable {L} [IsOrdered L] {n : ℕ}
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