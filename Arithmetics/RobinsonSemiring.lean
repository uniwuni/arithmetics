import Arithmetics.RobinsonModels
import Arithmetics.Relativization
import Mathlib.Logic.Equiv.Basic
variable {α : Type*}
namespace FirstOrder
namespace Arith.Robinson

open Language.Theory
open Language arith Structure 

instance : AtMostBinaryFunctions arith where
  at_most_binary n f := by
    rcases f <;> simp

  
  

section
variable {R : Type} [Add R] [Mul R] [LE R] [One R] [Zero R] [CompatibleOrderedSemiring R] {n : ℕ}
variable [RobinsonStructure R]
open RobinsonStructure
open CompatibleOrderedSemiring

local instance rModels : R ⊨ Q := by rw[satisfies_robinson_iff]; infer_instance

namespace Relativizer
def addAssociativityForm (z : R) := ∀ x : R, ∀ y : R, (x + y) + z = x + (y + z)
def addAssociativityForm' : arith.Formula (Fin 1) := ∀'∀'(((&0 + &1) + var (Sum.inl 0)) =' (&0 + (&1 + var (Sum.inl 0))))
  

  

@[simp] lemma addAssociativityForm'_iff (z : Fin 1 → R) :
  addAssociativityForm'.Realize (M := R) z ↔ addAssociativityForm (z 0) := by
  simp[addAssociativityForm',addAssociativityForm]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  simp[Fin.snoc]

@[simp] lemma addAssociativity_zero : addAssociativityForm (0 : R) := by simp[addAssociativityForm]
lemma addAssociativity_succ {z : R} (h : addAssociativityForm z) : addAssociativityForm (z + 1) := by
  intro x y
  rw[add_succ, h, ← add_succ, ← add_succ]

lemma addAssociativity_pred {z : R} (h : addAssociativityForm z) : addAssociativityForm (pred z) := by
  intro x y
  simp only [addAssociativityForm, add_succ, succ_inj] at h 
  rcases zero_or_succ z with (⟨eq⟩|⟨z2, eq⟩)
  · rw[eq]; simp 
  · rw[eq]; simp; rw[← succ_inj, ← add_succ, ← eq, h, ← add_succ, ← add_succ, ← eq]

@[simp] lemma addAssociativity_add {z1 z2 : R} (h1 : addAssociativityForm z1) (h2 : addAssociativityForm z2) :
  addAssociativityForm (z1 + z2) := by
  intro x y
  unfold addAssociativityForm at h1 h2 
  rw[←h2,h1,h2,h2]


def distributivityForm (z : R) := ∀ x : R, ∀ y : R, addAssociativityForm x → x * (y + z) = x * y + x * z
/-- theres no way this genuinely worked what the hell -/
def distributivityForm' : arith.Formula (Fin 1) :=
  ∀'(∀' (BoundedFormula.relabel (λ _ ↦ (Sum.inr 0 : Fin 1 ⊕ Fin 2)) addAssociativityForm' ⟹ ((&0 * (&1 + var (Sum.inl 0))) =' ((&0 * &1) + (&0 * var (Sum.inl 0))))))
    
@[simp] lemma distributivityForm'_iff (z : Fin 1 → R) :
  distributivityForm'.Realize (M := R) z ↔ distributivityForm (z 0) := by
  simp only [distributivityForm', Function.comp_apply, distributivityForm, addAssociativityForm']
  apply forall_congr'
  intro x
  simp only [BoundedFormula.relabel_all, Nat.add_eq, Nat.add_zero, Fin.snoc, Fin.coe_fin_one, lt_self_iff_false,
    Fin.castSucc_castLT, cast_eq, dite_false, BoundedFormula.realize_imp, BoundedFormula.realize_all, zero_add,
    Nat.lt_one_iff, dite_eq_ite, Fin.coe_castLT, BoundedFormula.realize_relabel, BoundedFormula.realize_bdEqual,
    realize_add, Term.realize_var, Sum.elim_inr, Function.comp_apply, ite_false, ite_true, Sum.elim_inl, realize_mul,
    addAssociativityForm]
 
  
@[simp] lemma distributivity_zero : distributivityForm (0 : R) := by simp[distributivityForm]
lemma distributivity_succ {z : R} (h : distributivityForm z) : distributivityForm (z + 1) := by
  intro x y h2
  rw[add_succ, mul_succ, h, h2, mul_succ]
  exact h2


def mulAssociativityForm (z : R) :=
  ∀ x : R, ∀ y : R, addAssociativityForm x → distributivityForm y → (x * y) * z = x * (y * z) 
def mulAssociativityForm' : arith.Formula (Fin 1) :=
  ∀'(∀' (BoundedFormula.relabel (λ _ ↦ (Sum.inr 0 : Fin 1 ⊕ Fin 2)) addAssociativityForm' ⟹ BoundedFormula.relabel (λ _ ↦ (Sum.inr 1 : Fin 1 ⊕ Fin 2)) distributivityForm' ⟹
      (((&0 * &1) * var (Sum.inl 0)) =' (&0 * (&1 * var (Sum.inl 0))))))

@[simp] lemma mulAssociativityForm'_iff (z : Fin 1 → R) :
  mulAssociativityForm'.Realize (M := R) z ↔ mulAssociativityForm (z 0) := by
  simp only [mulAssociativityForm', Function.comp_apply, mulAssociativityForm]
  apply forall_congr'
  intro x
  simp[BoundedFormula.realize_iff_formula_realize, Fin.snoc]

@[simp]
def mulAssociativity_zero : mulAssociativityForm (0 : R) := by simp[mulAssociativityForm]

def mulAssociativity_succ {z : R} (h : mulAssociativityForm z) : mulAssociativityForm (z + 1) := by
  intro x y h1 h2
  rw[mul_succ, h, ← h2, mul_succ] 
  · exact h1
  · exact h1
  · exact h2


def zeroIdentityForm (z : R) := ∀ y : R, (0 : R) + y = z → y = z 
def zeroIdentityForm' : arith.Formula (Fin 1) :=
  ∀' ((0 + &0) =' var (Sum.inl 0) ⟹ &0 =' var (Sum.inl 0))

@[simp] lemma zeroIdentityForm'_iff (z : Fin 1 → R) :
  zeroIdentityForm'.Realize (M := R) z ↔ zeroIdentityForm (z 0) := by
  simp only [zeroIdentityForm', Function.comp_apply, zeroIdentityForm]
  rfl

@[simp]
def zeroIdentity_zero : zeroIdentityForm (0 : R) := by simp[zeroIdentityForm]

def zeroIdentity_succ {z : R} (h : zeroIdentityForm z) : zeroIdentityForm (z + 1) := by
  intro x y
  rcases zero_or_succ x with (⟨eq⟩|⟨x2, eq⟩)
  · simp only [eq, RobinsonStructure.add_zero] at y 
    exfalso
    exact succ_ne_zero y.symm
  · rw[eq] at y
    simp only [add_succ, succ_inj] at y 
    specialize h x2 y
    rwa[← h]

def zeroIdentity_prop {z : R} (h : zeroIdentityForm (0 + z)) : z = 0 + z := h z rfl

namespace Layers
class Inductive (φ : arith.Formula (α ⊕ Fin 1)) (v : α → R) :=
  at_zero : φ.Realize (M := R) (Sum.elim v (λ _ ↦ (0 : R)))
  at_succ : ∀ x, φ.Realize (M := R) (Sum.elim v (λ _ ↦ (x : R))) → φ.Realize (M := R) (Sum.elim v (λ _ ↦ (x + 1: R)))

variable (φ : arith.Formula (α ⊕ Fin 1)) (v : α → R)
def c0Form (z : R) :=
  φ.Realize (M := R) (Sum.elim v (λ _ ↦ z)) ∧ addAssociativityForm z ∧ distributivityForm z
    ∧ mulAssociativityForm z ∧ zeroIdentityForm z

def c0Form' : arith.Formula (α ⊕ Fin 1) :=
  φ ⊓ (addAssociativityForm' ⊓ distributivityForm' ⊓ mulAssociativityForm' ⊓ zeroIdentityForm').relabel Sum.inr

@[simp] lemma c0Form'_iff (z : Fin 1 → R) :
  (c0Form' φ).Realize (M := R) (Sum.elim v z) ↔ c0Form (v := v) φ (z 0) := by
  simp only [c0Form', Formula.realize_inf, addAssociativityForm'_iff, distributivityForm'_iff,
    mulAssociativityForm'_iff, zeroIdentityForm'_iff, c0Form]
  suffices h : (fun _ => z 0) = (z : Fin 1 → R) by
    rw[h]
    simp only [Formula.realize_relabel, Sum.elim_comp_inr, Formula.realize_inf, addAssociativityForm'_iff,
      distributivityForm'_iff, mulAssociativityForm'_iff, zeroIdentityForm'_iff, and_congr_right_iff]
    tauto
  rw[← Fin.one_is_const]

def c1Form (x : R) :=
  ∀ y, ∀ z : R, y + z = x → addAssociativityForm z → c0Form φ v y 

def c1Form' : arith.Formula (α ⊕ Fin 1) :=
  ∀' ∀' ((&0 + &1) =' var (Sum.inl (Sum.inr 0)) ⟹
    BoundedFormula.relabel (λ _ ↦ (Sum.inr 1 : _ ⊕ Fin 2)) addAssociativityForm' ⟹
    BoundedFormula.relabel (Sum.map Sum.inl (λ _ ↦ (0 : Fin 2))) (c0Form' φ))

@[simp] lemma c1Form'_iff (z : Fin 1 → R) :
  (c1Form' φ).Realize (M := R) (Sum.elim v z) ↔ c1Form φ v (z 0) := by
  simp only [c1Form', Function.comp_apply, c1Form]
  apply forall_congr'
  intro y
  apply forall_congr'
  intro z
  simp only [Fin.snoc, zero_add, Nat.lt_one_iff, Fin.castSucc_castLT, Fin.coe_fin_one, lt_self_iff_false,
    Fin.coe_castLT, cast_eq, dite_false, dite_eq_ite, BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual,
    realize_add, Term.realize_var, Sum.elim_inr, ite_true, ite_false, Sum.elim_inl, BoundedFormula.realize_relabel,
    Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp.right_id]
  rw[iff_iff_eq]
  congr
  rw[BoundedFormula.realize_iff_formula_realize]
  rw[Sum.elim_comp_map]
  dsimp only [Sum.elim_comp_inl]
  rw[c0Form'_iff]
  congr

def c2Form (x : R) :=
  ∀ y, c1Form φ v y → c1Form φ v (y + x)

def c2Form' : arith.Formula (α ⊕ Fin 1)  :=
  ∀'
  (BoundedFormula.relabel (Sum.map Sum.inl λ _ ↦ (0 : Fin 1))
    (c1Form' φ) ⟹
   BoundedFormula.relabel (Equiv.sumAssoc _ _ (Fin 1)).invFun
     (BoundedFormula.subst (c1Form' φ)
       (Sum.elim (var ∘ (Sum.inl : α → α ⊕ _)) (λ _ ↦ var (Sum.inr (Sum.inr 0)) + var (Sum.inr (Sum.inl 0)) : _ → arith.Term (α ⊕ (Fin 1 ⊕ Fin 1))))))

@[simp] lemma c2Form'_iff (z : Fin 1 → R) :
  (c2Form' φ).Realize (M := R) (Sum.elim v z) ↔ c2Form φ v (z 0) := by
  simp only [c2Form', c2Form]
  apply forall_congr'
  intro y
  simp only [Fin.snoc, Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, cast_eq, dite_false,
    BoundedFormula.realize_imp, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp.right_id, BoundedFormula.realize_iff_formula_realize, c1Form'_iff, Function.comp_apply, Sum.elim_inr]
  rw[iff_iff_eq]
  congr
  · rw[Sum.elim_comp_map, c1Form'_iff]
    simp
  · rw[Formula.Realize, BoundedFormula.realize_subst]
    simp only [Equiv.sumAssoc, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, eq_iff_iff]
    have h : (y + z 0) = (λ _ ↦ y + z 0) 0 := rfl 
    rw[h, ← c1Form'_iff (z := (fun _ => y + z 0)), ← Formula.Realize]
    congr! with x
    rcases x with x|_
    · simp
    · simp 




def c3Form (x : R) :=
  c2Form φ v x ∧ (∀ y, c2Form φ v y → c2Form φ v (y * x))

def c3Form' : arith.Formula (α ⊕ Fin 1) :=
  c2Form' φ ⊓
  ∀'(BoundedFormula.relabel (Sum.map Sum.inl λ _ ↦ (0 : Fin 1))
    (c2Form' φ) ⟹
   BoundedFormula.relabel (Equiv.sumAssoc _ _ (Fin 1)).invFun
     (BoundedFormula.subst (c2Form' φ)
       (Sum.elim (var ∘ (Sum.inl : α → α ⊕ _)) (λ _ ↦ var (Sum.inr (Sum.inr 0)) * var (Sum.inr (Sum.inl 0)) : _ → arith.Term (α ⊕ (Fin 1 ⊕ Fin 1))))))

@[simp] lemma c3Form'_iff (z : Fin 1 → R) :
  (c3Form' φ).Realize (M := R) (Sum.elim v z) ↔ c3Form φ v (z 0) := by
  simp only [c3Form', Formula.realize_inf, c2Form'_iff, c3Form, and_congr_right_iff]
  intro _
  apply forall_congr'
  intro y
  simp only [Equiv.invFun_as_coe, BoundedFormula.realize_imp, BoundedFormula.realize_relabel, Nat.add_zero,
    Fin.castAdd_zero, Fin.cast_refl, Function.comp.right_id]
  apply imp_congr
  · rw[BoundedFormula.realize_iff_formula_realize, Sum.elim_comp_map, c2Form'_iff]
    simp
  · rw[BoundedFormula.realize_subst]
    have h : (y * z 0) = (λ _ ↦ y * z 0) 0 := rfl 
    rw[BoundedFormula.realize_iff_formula_realize, h, ← c2Form'_iff (z := (fun _ => y * z 0))]
    rw[iff_iff_eq]
    congr! with i
    rcases i with i|_
    · simp
    · simp
    
section
variable [Inductive φ v]

lemma c_of_c0 {x : R} (h : c0Form (R := R) φ v x) : φ.Realize (M := R) (Sum.elim v (λ _ ↦ (x : R))) := by
  unfold c0Form at h
  tauto

@[simp]
lemma c0_zero : c0Form (R := R) φ v 0 := by
  simp only [c0Form, addAssociativity_zero, distributivity_zero, mulAssociativity_zero, zeroIdentity_zero, and_self,
    and_true]
  exact Inductive.at_zero

lemma c0_succ {x : R} (h : c0Form φ v x) : c0Form φ v (x + 1) := by
  simp only [c0Form] at *
  split_ands
  · exact Inductive.at_succ _ h.left
  · simp[h, addAssociativity_succ] 
  · simp[h, distributivity_succ] 
  · simp[h, mulAssociativity_succ] 
  · simp[h, zeroIdentity_succ] 

lemma c0_of_c1 {x : R} (h : c1Form φ v x) : c0Form φ v x := by
  simp only [c1Form] at h 
  exact h x 0 (by simp) (by simp)

@[simp]
lemma c1_zero : c1Form (R := R) φ v 0 := by
  intro y z eq _
  simp only [add_zero_iff_both] at eq 
  rw[eq.left]
  apply c0_zero _ v

lemma c1_succ {x : R} (h : c1Form φ v x) : c1Form φ v (x + 1) := by
  intro y z h1 h2
  rcases zero_or_succ z with (⟨eq⟩|⟨z2, eq⟩)
  · rw[eq, RobinsonStructure.add_zero] at h1
    rw[h1]
    apply c0_succ φ v
    apply c0_of_c1 _ v h
  · rw[eq, add_succ] at h1
    have h1 := succ_inj.mp h1
    apply h (z := z2) _ h1
    convert addAssociativity_pred h2
    simp[eq]

lemma c1_summands {u w : R} (h : c1Form φ v (u + w)) (h2 : addAssociativityForm w) : c1Form φ v u := by
  intro y z eq assoc
  have : y + (z + w) = u + w := by rw[← eq, h2 y z]
  have assoc2 : addAssociativityForm (z + w) := addAssociativity_add assoc h2
  exact h (z := z + w) _ this assoc2 

lemma c1_of_c2 {x : R} (h : c2Form φ v x) : c1Form φ v x := by
  unfold c2Form at h
  have h2 := h 0 (c1_zero _ v)
  have h3 : zeroIdentityForm (0 + x) := by have := c0_of_c1 _ v h2; unfold c0Form at this; tauto
  rw[← zeroIdentity_prop h3] at h2
  exact h2

@[simp]
lemma c2_zero : c2Form (R := R) φ v 0 := by
  intro y h
  simpa

lemma c2_succ {x : R} (h : c2Form φ v x) : c2Form φ v (x + 1) := by
  intro y h2
  specialize h y h2
  simp only [add_succ]
  apply c1_succ _ v h

lemma c2_summands {u w : R} (h : c2Form φ v (u + w)) (h2 : addAssociativityForm w) : c2Form φ v u := by
  intro y h3
  apply c1_summands φ v (w := w)
  rw[h2]
  apply h _ h3
  apply h2

lemma c2_add {x y : R} (hx : c2Form φ v x) (hy : c2Form φ v y) : c2Form φ v (x + y) := by
  intro z hz
  have h3 : addAssociativityForm y := by have := c0_of_c1 φ v (c1_of_c2 φ v hy); unfold c0Form at this; tauto
  rw[← h3]
  apply hy
  exact hx _ hz

lemma c2_of_c3 {x : R} (h : c3Form φ v x) : c2Form φ v x := h.left

@[simp]
lemma c3_zero : c3Form (R := R) φ v 0 := by
  apply And.intro (c2_zero φ v)
  simp

lemma c3_succ {x : R} (h : c3Form φ v x) : c3Form φ v (x + 1) := by
  apply And.intro (c2_succ φ v (c2_of_c3 φ v h))
  intro y hy
  simp only [mul_succ]
  apply c2_add φ v
  · apply h.right _ hy 
  · exact hy 

lemma c3_pred {x : R} (h : c3Form φ v x) : c3Form φ v (pred x) := by
  rcases zero_or_succ x with (⟨eq⟩|⟨x2, eq⟩)
  · rw[eq]
    simp only [pred_zero, c3_zero]
  · rw[eq]
    rw[eq] at h
    simp only [pred_succ]
    constructor
    · apply c2_summands (w := 1)
      · exact c2_of_c3 _ _ h
      · rw[← succ_zero_eq_one]
        apply addAssociativity_succ
        simp
    · intro y hy
      have h2 := h.right y hy
      simp only [mul_succ] at h2
      apply c2_summands (w := y)
      · exact h2
      · have := c0_of_c1 _ v (c1_of_c2 _ v hy)
        unfold c0Form at this
        tauto

lemma c3_add {x y : R} (hx : c3Form φ v x) (hy : c3Form φ v y) : c3Form φ v (x + y) := by
  apply And.intro (c2_add _ v (c2_of_c3 _ _ hx) (c2_of_c3 _ _ hy))
  intro z hz
  have t1 : distributivityForm y := by have := c0_of_c1 _ v (c1_of_c2 _ v (c2_of_c3 _ v hy)); unfold c0Form at this; tauto
  have t2 : addAssociativityForm z := by have := c0_of_c1 _ v (c1_of_c2 _ v hz); unfold c0Form at this; tauto
  rw[t1 _ _ t2]
  apply c2_add _ v
  · apply hx.right _ hz
  · apply hy.right _ hz

lemma c3_mul {x y : R} (hx : c3Form φ v x) (hy : c3Form φ v y) : c3Form φ v (x * y) := by
  apply And.intro
  · apply hy.right
    apply c2_of_c3 _ _ hx
  · intro z hz
    have t1 : mulAssociativityForm y := by have := c0_of_c1 _ v (c1_of_c2 _ v (c2_of_c3 _ v hy)); unfold c0Form at this; tauto
    have t2 : distributivityForm x := by have := c0_of_c1 _ v (c1_of_c2 _ v (c2_of_c3 _ v hx)); unfold c0Form at this; tauto
    have t3 : addAssociativityForm z := by have := c0_of_c1 _ v (c1_of_c2 _ v hz); unfold c0Form at this; tauto
    rw[← t1 _ _ t3 t2]
    apply hy.right
    apply hx.right
    exact hz

lemma c_of_c3 {x : R} (h : c3Form φ v x) : φ.Realize (M := R) (Sum.elim v (λ _ ↦ (x : R))) := by
  apply c_of_c0
  apply c0_of_c1
  apply c1_of_c2 _ _
  apply c2_of_c3 _ _ h

instance c3Closed : BoundedFormula.ClosedUnderFunctions (L := arith) (R := R) (c3Form' φ) (k := v) where
  isClosedUnderFunctions := by
    intro n f
    rcases f
    · simp only [BoundedFormula.realize_closed_under_function_iff₂, funMap_add, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
      intro x y hx hy
      rw[c3Form'_iff] at *
      apply c3_add _ _ hx hy
    · simp only [BoundedFormula.realize_closed_under_function_iff₂, funMap_add, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
      intro x y hx hy
      rw[c3Form'_iff] at *
      apply c3_mul _ _ hx hy
    · simp
    · simp only [BoundedFormula.realize_closed_under_function_iff₀, funMap_one, c3Form'_iff]
      rw[← succ_zero_eq_one]
      apply c3_succ
      apply c3_zero

 
variable (v_in : ∀ i, v i ∈ BoundedFormula.RelativizationSubstructure₂' (R := R) (c3Form' φ) v) 

instance c3Model : BoundedFormula.RelativizationSubstructure₂' (R := R) (c3Form' φ) v ⊨ Q where
  realize_of_mem := by
    intro ψ ψ_in
    rcases ψ_in with ⟨h⟩
    · rw[h, Sentence.Realize, Formula.Realize]
      suffices h2 : BoundedFormula.Realize (M := { x // x ∈ BoundedFormula.RelativizationSubstructure₂' (c3Form' φ) v }) (BoundedFormula.relabel (default : Empty → α ⊕ Fin 0) axiom_succ_ne_zero) (λ i ↦ ⟨v i, v_in i⟩) finZeroElim by
        simp only [Nat.add_zero, BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl,
          Function.comp.right_id] at h2 
        congr!
      apply[BoundedFormula.relativizationSubstructure_universal_of]
        
       


end
end Layers


end Relativizer
end
end Arith.Robinson

end FirstOrder
