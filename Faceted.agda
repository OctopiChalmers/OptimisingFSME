open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty hiding (⊥)
open import Data.Product
open import Data.List
open import Lattices
import LatticeContexts
module Faceted (L₀ : Lattice) where

open LatticeEverything L₀
open LatticeContexts L₀

data Faceted (A : Set) : Set where
  raw : A → Faceted A
  <_*_∶_> : (ℓ : L) → Faceted A → Faceted A → Faceted A

_↓_ : ∀{A : Set} → Faceted A → L → A
raw x ↓ ℓ = x
< x * t₀ ∶ t₁ > ↓ ℓ with (x ?⊑ ℓ)
... | yes p = t₀ ↓ ℓ
... | no ¬p = t₁ ↓ ℓ

-- Semantic notion of equivalence
_~_ : ∀{A : Set} → Faceted A → Faceted A → Set
t₀ ~ t₁ = ∀(ℓ : L) → t₀ ↓ ℓ ≡ t₁ ↓ ℓ

-- Nice syntax for equational reasoning, originally due to Ulf
infix  3 _∎
infixr 2 _~⟨_⟩_
infix  1 begin_

data _IsRelatedTo_ {A : Set}(x y : Faceted A) : Set where
  relTo : (xy : (x ~ y)) → x IsRelatedTo y

begin_ : ∀{A : Set}{x y : Faceted A} → x IsRelatedTo y → x ~ y
begin relTo xy = xy

_~⟨_⟩_ : ∀{A : Set} (x : Faceted A) {y z} → x ~ y → y IsRelatedTo z → x IsRelatedTo z
_ ~⟨ xy ⟩ relTo yz = relTo λ ℓ → trans (xy ℓ) (yz ℓ)

_∎ : ∀{A : Set} (x : Faceted A) → x IsRelatedTo x
_∎ {A} x = relTo (λ ℓ → refl)

squash-right : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
             → ℓ₀ ⊑ ℓ₁ → < ℓ₀ * x₀ ∶ < ℓ₁ * x₁ ∶ x₂ > > ~ < ℓ₀ * x₀ ∶ x₂ >
squash-right {ℓ₀ = ℓ₀} {ℓ₁} x ℓ with ℓ₀ ?⊑ ℓ
... | yes p = refl
... | no ¬p with ℓ₁ ?⊑ ℓ
... | yes q = ⊥-elim (¬p (⊑-transitive x q))
... | no ¬q = refl

congruence : ∀{A : Set}{x₀ x₀' x₁ x₁' : Faceted A}{ℓ : L}
           → x₀ ~ x₀' → x₁ ~ x₁' → < ℓ * x₀ ∶ x₁ > ~ < ℓ * x₀' ∶ x₁' >
congruence {ℓ = ℓ} x x₂ ℓ₁ with ℓ ?⊑ ℓ₁
... | yes p = x ℓ₁
... | no ¬p = x₂ ℓ₁

left-move : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
          → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
          ~ < ℓ₁ * < ℓ₀ * x₀ ∶ x₂ > ∶ < ℓ₀ * x₁ ∶ x₂ > >
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ with ℓ₀ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p with ℓ₁ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ with ℓ₀ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ | yes p₂ = refl
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ | no ¬p = ⊥-elim (¬p p)
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | no ¬p with ℓ₀ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | yes p₁ = refl
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ p)
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p with ℓ₁ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | yes p with ℓ₀ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | yes p | yes p₁ = ⊥-elim (¬p p₁)
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | yes p | no ¬p₁ = refl
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ with ℓ₀ ?⊑ ℓ
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ | yes p = ⊥-elim (¬p p)
left-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ | no ¬p₂ = refl

right-move : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
           → < ℓ₀ * x₀ ∶ < ℓ₁ * x₁ ∶ x₂ > >
           ~ < ℓ₁ * < ℓ₀ * x₀ ∶ x₁ > ∶ < ℓ₀ * x₀ ∶ x₂ > >
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ with ℓ₀ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p with ℓ₁ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ with ℓ₀ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ | yes p₂ = refl
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ | no ¬p = ⊥-elim (¬p p)
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | no ¬p with ℓ₀ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | yes p₁ = refl
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ p)
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p with ℓ₁ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | yes p with ℓ₀ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | yes p | yes p₁ = ⊥-elim (¬p p₁)
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | yes p | no ¬p₁ = refl
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ with ℓ₀ ?⊑ ℓ
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ | yes p = ⊥-elim (¬p p)
right-move {ℓ₀ = ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ | no ¬p₂ = refl

⊥-irrelevance : ∀{A : Set}{x₀ x₁ : Faceted A}
              → x₀ ~ < ⊥ * x₀ ∶ x₁ >
⊥-irrelevance ℓ with ⊥ ?⊑ ℓ
... | yes p = refl
... | no ¬p = ⊥-elim (¬p ⊥-least)

collapse : ∀{A : Set}{x : Faceted A}{ℓ : L}
         → x ~ < ℓ * x ∶ x >
collapse {ℓ = ℓ} ℓ₁ with ℓ ?⊑ ℓ₁
... | yes p = refl
... | no ¬p = refl

right-duplicate : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ : L}
                → < ℓ * x₀ ∶ < ℓ * x₁ ∶ x₂ > >
                ~ < ℓ * x₀ ∶ x₂ >
right-duplicate {A} {x₀} {x₁} {x₂} {ℓ} ℓ₁ with ℓ ?⊑ ℓ₁
right-duplicate {A} {x₀} {x₁} {x₂} {ℓ} ℓ₁ | yes p = refl
right-duplicate {A} {x₀} {x₁} {x₂} {ℓ} ℓ₁ | no ¬p with ℓ ?⊑ ℓ₁
right-duplicate {A} {x₀} {x₁} {x₂} {ℓ} ℓ₁ | no ¬p | yes p = ⊥-elim (¬p p)
right-duplicate {A} {x₀} {x₁} {x₂} {ℓ} ℓ₁ | no ¬p | no ¬p₁ = refl

left-join : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
            → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
            ~ < (ℓ₀ ⊔ ℓ₁) * x₀ ∶ < ℓ₀ * x₁ ∶ x₂ > >
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ with ℓ₀ ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p with ℓ₁ ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ with (ℓ₀ ⊔ ℓ₁) ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ | yes p₂ = refl
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | yes p₁ | no ¬p = ⊥-elim (¬p (⊔-least-upper p p₁))
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | no ¬p with (ℓ₀ ⊔ ℓ₁) ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | yes p₁ =
  ⊥-elim (¬p (⊑-transitive ⊔-upper-bound (⊑-transitive (⊑-equality ⊔-commutative) p₁)))
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | no ¬p₁ with ℓ₀ ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | no ¬p₁ | yes p₁ = refl
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | yes p | no ¬p | no ¬p₁ | no ¬p₂ = ⊥-elim (¬p₂ p)
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | no ¬p with (ℓ₀ ⊔ ℓ₁) ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | no ¬p | yes p = ⊥-elim (¬p (⊑-transitive ⊔-upper-bound p))
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ with ℓ₀ ?⊑ ℓ
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ | yes p = ⊥-elim (¬p p)
left-join {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} ℓ | no ¬p | no ¬p₁ | no ¬p₂ = refl

label-replace : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ ℓ₁' : L}
              → ℓ₁' replaces ℓ₁ under ℓ₀
              → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
              ~ < ℓ₀ * < ℓ₁' * x₀ ∶ x₁ > ∶ x₂ >
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ with ℓ₀ ?⊑ ℓ
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p with ℓ₁ ?⊑ ℓ
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p | yes p₁ with ℓ₁' ?⊑ ℓ
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p | yes p₁ | yes p₂ = refl
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p | yes p₁ | no ¬p = ⊥-elim (¬p (proj₁ (x p) p₁))
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p | no ¬p with ℓ₁' ?⊑ ℓ
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p | no ¬p | yes p₁ = ⊥-elim (¬p (proj₂ (x p) p₁))
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | yes p | no ¬p | no ¬p₁ = refl
label-replace {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} {ℓ₁'} x ℓ | no ¬p = refl

{---------------- Derived Equivalences ----------------}
residuation : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
            → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
            ~ < ℓ₀ * < ℓ₁ ∶ ℓ₀ * x₀ ∶ x₁ > ∶ x₂ >
residuation = label-replace residual-replace 

residuation' : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₀' ℓ₁ : L}
             → ℓ₀' ⊑ ℓ₀
             → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
             ~ < ℓ₀ * < (ℓ₁ ∶ ℓ₀') ⊔ ℓ₀' * x₀ ∶ x₁ > ∶ x₂ >
residuation' p = label-replace λ p' → (λ q → ⊔-least-upper (⊑-transitive residuation-less-than q) (⊑-transitive p p'))
                                      , λ q → ⊑-transitive ∶-growing q

squash-left : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
            → ℓ₁ ⊑ ℓ₀
            → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
            ~ < ℓ₀ * x₀ ∶ x₂ >
squash-left {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} p =
  begin < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
  ~⟨ residuation ⟩
        < ℓ₀ * < ℓ₁ ∶ ℓ₀ * x₀ ∶ x₁ > ∶ x₂ >
  ~⟨ (λ ℓ → cong (λ ℓ' → < ℓ₀ * < ℓ' * x₀ ∶ x₁ > ∶ x₂ > ↓ ℓ) (⊥-residuation p)) ⟩
        < ℓ₀ * < ⊥ * x₀ ∶ x₁ > ∶ x₂ >
  ~⟨ congruence (λ ℓ → sym (⊥-irrelevance ℓ)) (λ ℓ → refl) ⟩
    < ℓ₀ * x₀ ∶ x₂ >
  ∎

left-duplicate : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ : L}
               → < ℓ * < ℓ * x₀ ∶ x₁ > ∶ x₂ >
               ~ < ℓ * x₀ ∶ x₂ >
left-duplicate = squash-left ⊑-reflexive

rotate : ∀{A : Set}{x₀ x₁ x₂ : Faceted A}{ℓ₀ ℓ₁ : L}
       → ℓ₀ ⊑ ℓ₁
       → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ > 
       ~ < ℓ₁ * x₀ ∶ < ℓ₀ * x₁ ∶ x₂ > >
rotate {A} {x₀} {x₁} {x₂} {ℓ₀} {ℓ₁} p =
  begin < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₂ >
  ~⟨ left-move ⟩
        < ℓ₁ * < ℓ₀ * x₀ ∶ x₂ > ∶ < ℓ₀ * x₁ ∶ x₂ > >
  ~⟨ squash-left p ⟩
        < ℓ₁ * x₀ ∶ < ℓ₀ * x₁ ∶ x₂ > >
  ∎

squash-left-left : ∀{A : Set}{x₀ x₁ x₂ x₃ : Faceted A}{ℓ₀ ℓ₁ ℓ₂}
                 → ℓ₂ ⊑ ℓ₀
                 → < ℓ₀ * < ℓ₁ * < ℓ₂ * x₀ ∶ x₁ > ∶ x₂ > ∶ x₃ >
                 ~ < ℓ₀ * < ℓ₁ * x₀ ∶ x₂ > ∶ x₃ >
squash-left-left {A} {x₀} {x₁} {x₂} {x₃} {ℓ₀} {ℓ₁} {ℓ₂} p =
  begin < ℓ₀ * < ℓ₁ * < ℓ₂ * x₀ ∶ x₁ > ∶ x₂ > ∶ x₃ >
  ~⟨ congruence left-move (λ ℓ → refl) ⟩
        < ℓ₀ * < ℓ₂ * < ℓ₁ * x₀ ∶ x₂ > ∶ < ℓ₁ * x₁ ∶ x₂ > > ∶ x₃ >
  ~⟨ squash-left p ⟩
        < ℓ₀ * < ℓ₁ * x₀ ∶ x₂ > ∶ x₃ >
  ∎

squash-left-right : ∀{A : Set}{x₀ x₁ x₂ x₃ : Faceted A}{ℓ₀ ℓ₁ ℓ₂}
                  → ℓ₂ ⊑ ℓ₀
                  → < ℓ₀ * < ℓ₁ * x₀ ∶ < ℓ₂ * x₁ ∶ x₂ > > ∶ x₃ >
                  ~ < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₃ >
squash-left-right {A} {x₀} {x₁} {x₂} {x₃} {ℓ₀} {ℓ₁} {ℓ₂} p =
  begin < ℓ₀ * < ℓ₁ * x₀ ∶ < ℓ₂ * x₁ ∶ x₂ > > ∶ x₃ >
  ~⟨ congruence right-move (λ ℓ → refl) ⟩
        < ℓ₀ * < ℓ₂ * < ℓ₁ * x₀ ∶ x₁ > ∶ < ℓ₁ * x₀ ∶ x₂ > > ∶ x₃ >
  ~⟨ squash-left p ⟩
        < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ x₃ >
  ∎

squash-right-right : ∀{A : Set}{x₀ x₁ x₂ x₃ : Faceted A}{ℓ₀ ℓ₁ ℓ₂}
                   → ℓ₀ ⊑ ℓ₂
                   → < ℓ₀ * x₀ ∶ < ℓ₁ * x₁ ∶ < ℓ₂ * x₂ ∶ x₃ > > >
                   ~ < ℓ₀ * x₀ ∶ < ℓ₁ * x₁ ∶ x₃ > >
squash-right-right {A} {x₀} {x₁} {x₂} {x₃} {ℓ₀} {ℓ₁} {ℓ₂} p =
  begin < ℓ₀ * x₀ ∶ < ℓ₁ * x₁ ∶ < ℓ₂ * x₂ ∶ x₃ > > >
  ~⟨ congruence (λ ℓ → refl) right-move ⟩
        < ℓ₀ * x₀ ∶ < ℓ₂ * < ℓ₁ * x₁ ∶ x₂ > ∶ < ℓ₁ * x₁ ∶ x₃ > > >
  ~⟨ squash-right p ⟩
        < ℓ₀ * x₀ ∶ < ℓ₁ * x₁ ∶ x₃ > >
  ∎

exchange : ∀{A : Set}{x₀ x₁ x₂ x₃ : Faceted A}{ℓ₀ ℓ₁ : L}
         → < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ < ℓ₁ * x₂ ∶ x₃ > >
         ~ < ℓ₁ * < ℓ₀ * x₀ ∶ x₂ > ∶ < ℓ₀ * x₁ ∶ x₃ > >
exchange {A} {x₀} {x₁} {x₂} {x₃} {ℓ₀} {ℓ₁} =
  begin < ℓ₀ * < ℓ₁ * x₀ ∶ x₁ > ∶ < ℓ₁ * x₂ ∶ x₃ > >
  ~⟨ left-move ⟩
        < ℓ₁ * < ℓ₀ * x₀ ∶ < ℓ₁ * x₂ ∶ x₃ > > ∶ < ℓ₀ * x₁ ∶ < ℓ₁ * x₂ ∶ x₃ > > >
  ~⟨ squash-left-right ⊑-reflexive ⟩
        < ℓ₁ * < ℓ₀ * x₀ ∶ x₂ > ∶ < ℓ₀ * x₁ ∶ < ℓ₁ * x₂ ∶ x₃ > > >
  ~⟨ squash-right-right ⊑-reflexive ⟩
        < ℓ₁ * < ℓ₀ * x₀ ∶ x₂ > ∶ < ℓ₀ * x₁ ∶ x₃ > >
  ∎

right-collapse : ∀{A : Set}{x₀ x₁ : Faceted A}{ℓ₀ ℓ₁ : L}
               → ℓ₀ ⊑ ℓ₁
               → < ℓ₁ * x₀ ∶ < ℓ₀ * x₀ ∶ x₁ > >
               ~ < ℓ₀ * x₀ ∶ x₁ >
right-collapse {A} {x₀} {x₁} {ℓ₀} {ℓ₁} p =
  begin < ℓ₁ * x₀ ∶ < ℓ₀ * x₀ ∶ x₁ > >
  ~⟨ (λ ℓ → cong (λ ℓ' → < ℓ' * x₀ ∶ < ℓ₀ * x₀ ∶ x₁ > > ↓ ℓ)
            (⊑-antisymmetric (⊑-transitive ⊔-upper-bound (⊑-equality ⊔-commutative)) (⊔-least-upper p ⊑-reflexive)))
   ⟩
        < (ℓ₀ ⊔ ℓ₁) * x₀ ∶ < ℓ₀ * x₀ ∶ x₁ > >
  ~⟨ (λ ℓ → sym (left-join ℓ)) ⟩
        < ℓ₀ * < ℓ₁ * x₀ ∶ x₀ > ∶ x₁ >
  ~⟨ congruence (λ ℓ → sym (collapse ℓ)) (λ ℓ → refl) ⟩
        < ℓ₀ * x₀ ∶ x₁ >
  ∎

lub-xy : ∀{A}{x y : Faceted A}{ℓ₀ ℓ₁ : L}
       → < (ℓ₀ ⊔ ℓ₁) * x ∶ < ℓ₀ * y ∶ < ℓ₁ * x ∶ y > > > ~ < ℓ₁ * x ∶ y >
lub-xy {A} {x} {y} {ℓ₀} {ℓ₁} =
  begin < (ℓ₀ ⊔ ℓ₁) * x ∶ < ℓ₀ * y ∶ < ℓ₁ * x ∶ y > > >
  ~⟨ (λ ℓ → sym (left-join ℓ)) ⟩
        < ℓ₀ * < ℓ₁ * x ∶ y > ∶ < ℓ₁ * x ∶ y > >
  ~⟨ (λ ℓ → sym (collapse ℓ)) ⟩
        < ℓ₁ * x ∶ y > ∎

{---------------- Right Chaining ----------------}
data IsRightChain : ∀{A} → Faceted A → Set where
  Leaf : ∀{A}{a : A} → IsRightChain (raw a)
  Node : ∀{A}{a : A}{x : Faceted A}{ℓ : L} → IsRightChain x → IsRightChain < ℓ * raw a ∶ x >

-- < ℓ₀ * < ℓ₁ * f₀ ∶ f₁ > ∶ fc >
go : ∀{A : Set} → Faceted A → L → Faceted A → L → Faceted A → Faceted A
go (raw x) ℓ₁ (raw x₁) ℓ₀ fc = < ℓ₀ ⊔ ℓ₁ * raw x ∶ < ℓ₀ * raw x₁ ∶ fc > >
go (raw x) ℓ₁ < ℓ * f₁ ∶ f₂ > ℓ₀ fc = < ℓ₀ ⊔ ℓ₁ * raw x ∶ go f₁ ℓ f₂ ℓ₀ fc >
go < ℓ * f₀ ∶ f₂ > ℓ₁ (raw x) ℓ₀ fc = go f₀ ℓ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * raw x ∶ fc >
go < ℓ * f₀ ∶ f₂ > ℓ₁ < ℓ₂ * f₁ ∶ f₃ > ℓ₀ fc = go f₀ ℓ f₂ (ℓ₀ ⊔ ℓ₁) (go f₁ ℓ₂ f₃ ℓ₀ fc)

right-chain : ∀{A : Set} → Faceted A → Faceted A
right-chain (raw x) = raw x
right-chain < ℓ * raw x ∶ x₁ > = < ℓ * raw x ∶ right-chain x₁ >
right-chain < ℓ * < ℓ₁ * x ∶ x₂ > ∶ x₁ > = go x ℓ₁ x₂ ℓ (right-chain x₁)

-- Proofs
go-preserves-down : ∀{A : Set}
                  → (f₀ : Faceted A) → (ℓ₁ : L) → (f₁ : Faceted A)
                  → (ℓ₀ : L) → (fc : Faceted A) → (fc' : Faceted A)
                  → fc ~ fc'
                  → go f₀ ℓ₁ f₁ ℓ₀ fc ~ go f₀ ℓ₁ f₁ ℓ₀ fc'
go-preserves-down (raw x₁) ℓ₁ (raw x₂) ℓ₀ fc fc' x = congruence (λ ℓ → refl) (congruence (λ ℓ → refl) x)
go-preserves-down (raw x₁) ℓ₁ < ℓ₂ * f₁ ∶ f₂ > ℓ₀ fc fc' x =
  congruence (λ ℓ → refl) (go-preserves-down f₁ ℓ₂ f₂ ℓ₀ fc fc' x)
go-preserves-down < ℓ₂ * f₀ ∶ f₂ > ℓ₁ (raw x₁) ℓ₀ fc fc' x =
  go-preserves-down f₀ ℓ₂ f₂ (_⊔_ ℓ₀ ℓ₁) < ℓ₀ * raw x₁ ∶ fc > < ℓ₀ * raw x₁ ∶ fc' > (congruence (λ ℓ → refl) x)
go-preserves-down < ℓ₂ * f₀ ∶ f₂ > ℓ₁ < ℓ₃ * f₁ ∶ f₃ > ℓ₀ fc fc' x =
  go-preserves-down f₀ ℓ₂ f₂ (_⊔_ ℓ₀ ℓ₁) (go f₁ ℓ₃ f₃ ℓ₀ fc) (go f₁ ℓ₃ f₃ ℓ₀ fc') (go-preserves-down f₁ ℓ₃ f₃ ℓ₀ fc fc' x)

go-preserves-semantics : ∀{A : Set}
                       → (f₀ : Faceted A) → (ℓ₁ : L) → (f₁ : Faceted A)
                       → (ℓ₀ : L) → (fc : Faceted A)
                       → < ℓ₀ * < ℓ₁ * f₀ ∶ f₁ > ∶ fc > ~ go f₀ ℓ₁ f₁ ℓ₀ fc 
go-preserves-semantics (raw x₁) ℓ₁ (raw x₂) ℓ₀ fc = left-join
go-preserves-semantics (raw x₁) ℓ₁ < ℓ * f₁ ∶ f₂ > ℓ₀ fc =
  begin < ℓ₀ * < ℓ₁ * raw x₁ ∶ < ℓ * f₁ ∶ f₂ > > ∶ fc >
  ~⟨ left-join ⟩
        < ℓ₀ ⊔ ℓ₁ * raw x₁ ∶ < ℓ₀ * < ℓ * f₁ ∶ f₂ > ∶ fc > >
  ~⟨ congruence (λ ℓ → refl) (go-preserves-semantics f₁ ℓ f₂ ℓ₀ fc) ⟩
        < ℓ₀ ⊔ ℓ₁ * raw x₁ ∶ go f₁ ℓ f₂ ℓ₀ fc >
  ∎
go-preserves-semantics < ℓ₂ * f₀ ∶ f₂ > ℓ₁ (raw x₁) ℓ₀ fc =
  begin < ℓ₀ * < ℓ₁ * < ℓ₂ * f₀ ∶ f₂ > ∶ raw x₁ > ∶ fc >
  ~⟨ left-join ⟩
        < ℓ₀ ⊔ ℓ₁ * < ℓ₂ * f₀ ∶ f₂ > ∶ < ℓ₀ * raw x₁ ∶ fc > >
  ~⟨ go-preserves-semantics f₀ ℓ₂ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * raw x₁ ∶ fc > ⟩
        go f₀ ℓ₂ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * raw x₁ ∶ fc >
  ∎ 
go-preserves-semantics < ℓ₂ * f₀ ∶ f₂ > ℓ₁ < ℓ * f₁ ∶ f₃ > ℓ₀ fc =
  begin < ℓ₀ * < ℓ₁ * < ℓ₂ * f₀ ∶ f₂ > ∶ < ℓ * f₁ ∶ f₃ > > ∶ fc >
  ~⟨ left-join ⟩
        < ℓ₀ ⊔ ℓ₁ * < ℓ₂ * f₀ ∶ f₂ > ∶ < ℓ₀ * < ℓ * f₁ ∶ f₃ > ∶ fc > >
  ~⟨ go-preserves-semantics f₀ ℓ₂ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * < ℓ * f₁ ∶ f₃ > ∶ fc > ⟩
        go f₀ ℓ₂ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * < ℓ * f₁ ∶ f₃ > ∶ fc >
  ~⟨ go-preserves-down f₀ ℓ₂ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * < ℓ * f₁ ∶ f₃ > ∶ fc > (go f₁ ℓ f₃ ℓ₀ fc) (go-preserves-semantics f₁ ℓ f₃ ℓ₀ fc) ⟩
        go f₀ ℓ₂ f₂ (ℓ₀ ⊔ ℓ₁) (go f₁ ℓ f₃ ℓ₀ fc)
  ∎

go-makes-chain : ∀{A : Set}
               → (f₀ : Faceted A) → (ℓ₁ : L) → (f₁ : Faceted A)
               → (ℓ₀ : L) → (fc : Faceted A) → IsRightChain fc
               → IsRightChain (go f₀ ℓ₁ f₁ ℓ₀ fc)
go-makes-chain (raw x) ℓ₁ (raw x₁) ℓ₀ fc p = Node (Node p)
go-makes-chain (raw x) ℓ₁ < ℓ * f₁ ∶ f₂ > ℓ₀ fc p = Node (go-makes-chain f₁ ℓ f₂ ℓ₀ fc p)
go-makes-chain < ℓ * f₀ ∶ f₂ > ℓ₁ (raw x) ℓ₀ fc p = go-makes-chain f₀ ℓ f₂ (ℓ₀ ⊔ ℓ₁) < ℓ₀ * raw x ∶ fc > (Node p)
go-makes-chain < ℓ * f₀ ∶ f₂ > ℓ₁ < ℓ₂ * f₁ ∶ f₃ > ℓ₀ fc p =
  go-makes-chain f₀ ℓ f₂ (ℓ₀ ⊔ ℓ₁) (go f₁ ℓ₂ f₃ ℓ₀ fc) (go-makes-chain f₁ ℓ₂ f₃ ℓ₀ fc p)

right-chain-preserves-semantics : ∀{A : Set} → (f : Faceted A) → f ~ right-chain f
right-chain-preserves-semantics (raw x) = λ ℓ → refl
right-chain-preserves-semantics < ℓ * raw x ∶ f₁ > = congruence (λ ℓ₁ → refl) (right-chain-preserves-semantics f₁)
right-chain-preserves-semantics < ℓ * < ℓ₁ * f ∶ f₂ > ∶ f₁ > =
  begin < ℓ * < ℓ₁ * f ∶ f₂ > ∶ f₁ >
  ~⟨ congruence (λ ℓ₂ → refl) (right-chain-preserves-semantics f₁) ⟩
        < ℓ * < ℓ₁ * f ∶ f₂ > ∶ right-chain f₁ >
  ~⟨ go-preserves-semantics f ℓ₁ f₂ ℓ (right-chain f₁) ⟩
        go f ℓ₁ f₂ ℓ (right-chain f₁)
  ∎

right-chain-makes-chain : ∀{A : Set} → (f : Faceted A) → IsRightChain (right-chain f)
right-chain-makes-chain (raw x) = Leaf
right-chain-makes-chain < ℓ * raw x ∶ x₁ > = Node (right-chain-makes-chain x₁)
right-chain-makes-chain < ℓ * < ℓ₁ * x ∶ x₂ > ∶ x₁ > = go-makes-chain x ℓ₁ x₂ ℓ (right-chain x₁) (right-chain-makes-chain x₁)

{- Context Stuff -}
_~c⟨_⟩_ : ∀{A} → Faceted A → Context → Faceted A → Set
t₀ ~c⟨ γ ⟩ t₁ = ∀{ℓ : L} → ℓ inView γ → t₀ ↓ ℓ ≡ t₁ ↓ ℓ

~→~γ : ∀{A}{t₀ t₁ : Faceted A}{γ : Context} → t₀ ~ t₁ → t₀ ~c⟨ γ ⟩ t₁
~→~γ = λ z {ℓ} _ → z ℓ

~c[]→~ : ∀{A}{t₀ t₁ : Faceted A} → t₀ ~c⟨ [] ⟩ t₁ → t₀ ~ t₁
~c[]→~ = λ z ℓ → z vEmpty

~γ-left : ∀{A}{t₀ t₁ t₂ : Faceted A}{γ : Context}{ℓ : L} → t₀ ~c⟨ + ℓ ∷ γ ⟩ t₁ → < ℓ * t₀ ∶ t₂ > ~c⟨ γ ⟩ < ℓ * t₁ ∶ t₂ >
~γ-left {A} {t₀} {t₁} {t₂} {γ} {ℓ} x {ℓ₁} x₁ with ℓ ?⊑ ℓ₁
... | yes p = x (vPositive p x₁)
... | no ¬p = refl

~γ-right : ∀{A}{t₀ t₁ t₂ : Faceted A}{γ : Context}{ℓ : L} → t₀ ~c⟨ - ℓ ∷ γ ⟩ t₁ → < ℓ * t₂ ∶ t₀ > ~c⟨ γ ⟩ < ℓ * t₂ ∶ t₁ >
~γ-right {A} {t₀} {t₁} {t₂} {γ} {ℓ} x {ℓ₁} x₁ with ℓ ?⊑ ℓ₁
... | yes p = refl
... | no ¬p = x (vNegative ¬p x₁)

context-replace : ∀{A}{t₀ t₁ : Faceted A}{γ : Context}{ℓ' ℓ : L}
                → ℓ' replaces ℓ underContext γ → < ℓ * t₀ ∶ t₁ > ~c⟨ γ ⟩ < ℓ' * t₀ ∶ t₁ >
context-replace {ℓ' = ℓ'} {ℓ} x {ℓ₁} x₁ with ℓ ?⊑ ℓ₁
context-replace {ℓ' = ℓ'} {ℓ} x {ℓ₁} x₁ | yes p with ℓ' ?⊑ ℓ₁
... | yes p₁ = refl
... | no ¬p₁ = ⊥-elim (¬p₁ (proj₁ (x x₁) p))
context-replace {ℓ' = ℓ'} {ℓ} x {ℓ₁} x₁ | no ¬p with ℓ' ?⊑ ℓ₁
... | yes p₁ = ⊥-elim (¬p (proj₂ (x x₁) p₁))
... | no ¬p₁ = refl

context-left-squash : ∀{A : Set}{x₀ x₁ : Faceted A}{γ : Context}{ℓ : L} → ℓ ≼ γ → < ℓ * x₀ ∶ x₁ > ~c⟨ γ ⟩ x₀
context-left-squash {A} {x₀} {x₁} {γ} {ℓ} x {ℓ₁} x₂ with ℓ ?⊑ ℓ₁
... | yes p = refl
... | no ¬p = ⊥-elim (¬p (x x₂))

-- Simple corollary which justifies the "candidateLeftSquash" optimization in the Haskell implementation
candidate-left-squash : ∀{A : Set}{x₀ x₁ : Faceted A}{γ : Context}{ℓ : L} → ℓ ⊑ candidate γ → < ℓ * x₀ ∶ x₁ > ~c⟨ γ ⟩ x₀
candidate-left-squash p = context-left-squash (≼-from-candidate p)

context-right-squash : ∀{A : Set}{x₀ x₁ : Faceted A}{γ : Context}{ℓ : L} → ℓ / γ → < ℓ * x₀ ∶ x₁ > ~c⟨ γ ⟩ x₁
context-right-squash {A} {x₀} {x₁} {γ} {ℓ} x {ℓ₁} x₂ with ℓ ?⊑ ℓ₁
... | yes p = ⊥-elim (x x₂ p)
... | no ¬p = refl

context-residual : ∀{A : Set}{x₀ x₁ : Faceted A}{γ : Context}{ℓ : L} → < ℓ * x₀ ∶ x₁ > ~c⟨ γ ⟩ < ℓ ∶ candidate γ * x₀ ∶ x₁ >
context-residual {γ = γ} x = context-replace {γ = γ} residual-replace-context x
