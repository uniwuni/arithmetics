import Arithmetics.RobinsonModels
import Arithmetics.Relativization
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

local instance : R ⊨ Q := by rw[satisfies_robinson_iff]; infer_instance

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
variable (φ : arith.Formula (Fin 1))
def c0Form (z : R) :=
  φ.Realize (M := R) (λ _ ↦ z) ∧ addAssociativityForm z ∧ distributivityForm z
    ∧ mulAssociativityForm z ∧ zeroIdentityForm z

def c0Form' : arith.Formula (Fin 1) :=
  φ ⊓ addAssociativityForm' ⊓ distributivityForm' ⊓ mulAssociativityForm' ⊓ zeroIdentityForm'

@[simp] lemma c0Form'_iff (z : Fin 1 → R) :
  (c0Form' φ).Realize (M := R) z ↔ c0Form φ (z 0) := by
  simp only [c0Form', Formula.realize_inf, addAssociativityForm'_iff, distributivityForm'_iff,
    mulAssociativityForm'_iff, zeroIdentityForm'_iff, c0Form]
  suffices h : (fun _ => z 0) = (z : Fin 1 → R) by
    rw[h]
    tauto
  rw[← Fin.one_is_const]

def c1Form (x : R) :=
  ∀ y, ∀ z : R, y + z = x → addAssociativityForm z → c0Form φ y

def c1Form' : arith.Formula (Fin 1) :=
  ∀' ∀' ((&0 + &1) =' var (Sum.inl 0) ⟹
    BoundedFormula.relabel (λ _ ↦ (Sum.inr 1 : Fin 1 ⊕ Fin 2)) addAssociativityForm' ⟹
    BoundedFormula.relabel (λ _ ↦ (Sum.inr 0 : Fin 1 ⊕ Fin 2)) (c0Form' φ))

@[simp] lemma c1Form'_iff (z : Fin 1 → R) :
  (c1Form' φ).Realize (M := R) z ↔ c1Form φ (z 0) := by
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
  simp

def c2Form (x : R) :=
  ∀ y, c1Form φ y → c1Form φ (y + x)

def c2Form' : arith.Formula (Fin 1) :=
  ∀'
  (BoundedFormula.relabel (λ _ ↦ (Sum.inr 0 : Fin 1 ⊕ Fin 1))
    (c1Form' φ) ⟹
   BoundedFormula.relabel (id : Fin 1 ⊕ Fin 1 → _)
     (BoundedFormula.subst (c1Form' φ)
       (λ _ ↦ var (Sum.inr 0) + var (Sum.inl 0) : _ → arith.Term (Fin 1 ⊕ Fin 1))))

@[simp] lemma c2Form'_iff (z : Fin 1 → R) :
  (c2Form' φ).Realize (M := R) z ↔ c2Form φ (z 0) := by
  simp only [c2Form', c2Form]
  apply forall_congr'
  intro y
  simp only [Fin.snoc, Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, cast_eq, dite_false,
    BoundedFormula.realize_imp, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp.right_id, BoundedFormula.realize_iff_formula_realize, c1Form'_iff, Function.comp_apply, Sum.elim_inr]
  rw[iff_iff_eq]
  congr
  rw[Formula.Realize]
  rw[BoundedFormula.realize_subst]
  rw[← Formula.Realize]
  simp

def c3Form (x : R) :=
  c2Form φ x ∧ (∀ y, c2Form φ y → c2Form φ (y * x))

def c3Form' : arith.Formula (Fin 1) :=
  c2Form' φ ⊓
  ∀'(BoundedFormula.relabel (λ _ ↦  (Sum.inr 0 : Fin 1 ⊕ Fin 1)) (c2Form' φ) ⟹
     BoundedFormula.relabel (id : Fin 1 ⊕ Fin 1 → _)
     (BoundedFormula.subst (c2Form' φ)
       (λ _ ↦ var (Sum.inr 0) * var (Sum.inl 0) : _ → arith.Term (Fin 1 ⊕ Fin 1)))) 

@[simp] lemma c3Form'_iff (z : Fin 1 → R) :
  (c3Form' φ).Realize (M := R) z ↔ c3Form φ (z 0) := by
  simp only [c3Form', Formula.realize_inf, c2Form'_iff, c3Form, and_congr_right_iff]
  intro _
  apply forall_congr'
  intro y
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    Function.comp.right_id]
  apply imp_congr
  · rw[BoundedFormula.realize_iff_formula_realize]
    simp
  · rw[BoundedFormula.realize_subst]
    rw[BoundedFormula.realize_iff_formula_realize]
    simp
section
variable (φ0 : φ.Realize (M := R) (λ _ ↦ (0 : R))) (φs : ∀ x, φ.Realize (M := R) (λ _ ↦ x) → φ.Realize (M := R) (λ _ ↦ x + 1))


lemma c_of_c0 {x : R} (h : c0Form (R := R) φ x) : φ.Realize (M := R) (λ _ ↦ x) := by
  unfold c0Form at h
  tauto

@[simp]
lemma c0_zero : c0Form (R := R) φ 0 := by
  simp only [c0Form, addAssociativity_zero, distributivity_zero, mulAssociativity_zero, zeroIdentity_zero, and_self,
    and_true]
  exact φ0

lemma c0_succ {x : R} (h : c0Form φ x) : c0Form φ (x + 1) := by
  simp only [c0Form] at *
  split_ands
  · exact φs _ h.left
  · simp[h, addAssociativity_succ] 
  · simp[h, distributivity_succ] 
  · simp[h, mulAssociativity_succ] 
  · simp[h, zeroIdentity_succ] 

lemma c0_of_c1 {x : R} (h : c1Form φ x) : c0Form φ x := by
  simp only [c1Form] at h 
  exact h x 0 (by simp) (by simp)

@[simp]
lemma c1_zero : c1Form (R := R) φ 0 := by
  intro y z eq _
  simp only [add_zero_iff_both] at eq 
  rw[eq.left]
  apply c0_zero _ φ0 (R := R)

lemma c1_succ {x : R} (h : c1Form φ x) : c1Form φ (x + 1) := by
  intro y z h1 h2
  rcases zero_or_succ z with (⟨eq⟩|⟨z2, eq⟩)
  · rw[eq, RobinsonStructure.add_zero] at h1
    rw[h1]
    apply c0_succ φ φs
    apply c0_of_c1 _ h
  · rw[eq, add_succ] at h1
    have h1 := succ_inj.mp h1
    apply h (z := z2) _ h1
    convert addAssociativity_pred h2
    simp[eq]

lemma c1_summands {u v : R} (h : c1Form φ (u + v)) (h2 : addAssociativityForm v) : c1Form φ u := by
  intro y z eq assoc
  have : y + (z + v) = u + v := by rw[← eq, h2 y z]
  have assoc2 : addAssociativityForm (z + v) := addAssociativity_add assoc h2
  exact h (z := z + v) _ this assoc2 

lemma c1_of_c2 {x : R} (h : c2Form φ x) : c1Form φ x := by
  unfold c2Form at h
  have h2 := h 0 (c1_zero _ φ0)
  have h3 : zeroIdentityForm (0 + x) := by have := c0_of_c1 _ h2; unfold c0Form at this; tauto
  rw[← zeroIdentity_prop h3] at h2
  exact h2

@[simp]
lemma c2_zero : c2Form (R := R) φ 0 := by
  intro y h
  simpa

lemma c2_succ {x : R} (h : c2Form φ x) : c2Form φ (x + 1) := by
  intro y h2
  specialize h y h2
  simp only [add_succ]
  apply c1_succ _ φs h

lemma c2_summands {u v : R} (h : c2Form φ (u + v)) (h2 : addAssociativityForm v) : c2Form φ u := by
  intro y h3
  apply c1_summands φ (v := v)
  rw[h2]
  apply h _ h3
  apply h2

lemma c2_add {x y : R} (hx : c2Form φ x) (hy : c2Form φ y) : c2Form φ (x + y) := by
  intro z hz
  have h3 : addAssociativityForm y := by have := c0_of_c1 φ (c1_of_c2 φ φ0 hy); unfold c0Form at this; tauto
  rw[← h3]
  apply hy
  exact hx _ hz

lemma c2_of_c3 {x : R} (h : c3Form φ x) : c2Form φ x := h.left

@[simp]
lemma c3_zero : c3Form (R := R) φ 0 := by
  apply And.intro (c2_zero φ)
  simp

lemma c3_succ {x : R} (h : c3Form φ x) : c3Form φ (x + 1) := by
  apply And.intro (c2_succ φ φs (c2_of_c3 φ h))
  intro y hy
  simp only [mul_succ]
  apply c2_add φ φ0
  · apply h.right _ hy 
  · exact hy 

lemma c3_pred {x : R} (h : c3Form φ x) : c3Form φ (pred x) := by
  rcases zero_or_succ x with (⟨eq⟩|⟨x2, eq⟩)
  · rw[eq]
    simp only [pred_zero, c3_zero]
  · rw[eq]
    rw[eq] at h
    simp only [pred_succ]
    constructor
    · apply c2_summands (v := 1)
      · exact c2_of_c3 _ h
      · rw[← succ_zero_eq_one]
        apply addAssociativity_succ
        simp
    · intro y hy
      have h2 := h.right y hy
      simp only [mul_succ] at h2
      apply c2_summands (v := y)
      · exact h2
      · have := c0_of_c1 _ (c1_of_c2 _ φ0 hy)
        unfold c0Form at this
        tauto

lemma c3_add {x y : R} (hx : c3Form φ x) (hy : c3Form φ y) : c3Form φ (x + y) := by
  apply And.intro (c2_add _ φ0 (c2_of_c3 _ hx) (c2_of_c3 _ hy))
  intro z hz
  have t1 : distributivityForm y := by have := c0_of_c1 _ (c1_of_c2 _ φ0 (c2_of_c3 _ hy)); unfold c0Form at this; tauto
  have t2 : addAssociativityForm z := by have := c0_of_c1 _ (c1_of_c2 _ φ0 hz); unfold c0Form at this; tauto
  rw[t1 _ _ t2]
  apply c2_add _ φ0
  · apply hx.right _ hz
  · apply hy.right _ hz

lemma c3_mul {x y : R} (hx : c3Form φ x) (hy : c3Form φ y) : c3Form φ (x * y) := by
  apply And.intro
  · apply hy.right
    apply c2_of_c3 _ hx
  · intro z hz
    have t1 : mulAssociativityForm y := by have := c0_of_c1 _ (c1_of_c2 _ φ0 (c2_of_c3 _ hy)); unfold c0Form at this; tauto
    have t2 : distributivityForm x := by have := c0_of_c1 _ (c1_of_c2 _ φ0 (c2_of_c3 _ hx)); unfold c0Form at this; tauto
    have t3 : addAssociativityForm z := by have := c0_of_c1 _ (c1_of_c2 _ φ0 hz); unfold c0Form at this; tauto
    rw[← t1 _ _ t3 t2]
    apply hy.right
    apply hx.right
    exact hz

lemma c_of_c3 {x : R} (h : c3Form φ x) : φ.Realize (M := R) (λ _ ↦ x) := by
  apply c_of_c0
  apply c0_of_c1
  apply c1_of_c2 _ φ0
  apply c2_of_c3 _ h


end
end Layers


end Relativizer
end
end Arith.Robinson

end FirstOrder
