open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
module Lattices where

record Lattice : Set₁ where
  field
    L : Set
    ⊥ : L
    ⊤ : L
    _⊑_ : L → L → Set
    _⊔_ : L → L → L
    -- Residuation
    _∶_ : L → L → L

    -- Laws about ⊥ and ⊤
    ⊥-least  : ∀{ℓ} → ⊥ ⊑ ℓ
    ⊥-unit   : ∀{ℓ} → ⊥ ⊔ ℓ ≡ ℓ
    ⊤-most   : ∀{ℓ} → ℓ ⊑ ⊤
    ⊤-absorb : ∀{ℓ} → ⊤ ⊔ ℓ ≡ ⊤

    -- Laws about _⊑_
    ⊑-reflexive     : ∀{ℓ} → ℓ ⊑ ℓ
    ⊑-transitive    : ∀{ℓ ℓ' ℓ''} → ℓ ⊑ ℓ' → ℓ' ⊑ ℓ'' → ℓ ⊑ ℓ''
    ⊑-antisymmetric : ∀{ℓ ℓ'} → ℓ ⊑ ℓ' → ℓ' ⊑ ℓ → ℓ ≡ ℓ'
    ⊑-thin          : ∀{ℓ ℓ'}{p₀ p₁ : ℓ ⊑ ℓ'} → p₀ ≡ p₁

    -- Laws about _⊔_
    ⊔-commutative : ∀{ℓ ℓ'} → ℓ ⊔ ℓ' ≡ ℓ' ⊔ ℓ
    ⊔-associative : ∀{ℓ ℓ' ℓ''} → ((ℓ ⊔ ℓ') ⊔ ℓ'') ≡ ℓ ⊔ (ℓ' ⊔ ℓ'')
    ⊔-upper-bound : ∀{ℓ ℓ'} → ℓ ⊑ (ℓ ⊔ ℓ')
    ⊔-least-upper : ∀{ℓ ℓ' ℓ''} → ℓ ⊑ ℓ'' → ℓ' ⊑ ℓ'' → (ℓ ⊔ ℓ') ⊑ ℓ''

    -- To make auto less dumb
    ⊑-equality : ∀{ℓ ℓ'} → ℓ ≡ ℓ' → ℓ ⊑ ℓ'

    -- Laws about _∶_
    ∶-growing   : ∀{ℓ ℓ'} → ℓ ⊑ ((ℓ ∶ ℓ') ⊔ ℓ')
    ∶-left-move : ∀{ℓ ℓ' ℓ''} → ℓ ⊑ (ℓ' ⊔ ℓ'') → (ℓ ∶ ℓ') ⊑ ℓ''

    -- Decidability criteria
    _≟_  : (ℓ ℓ' : L) → Dec (ℓ ≡ ℓ')
    _?⊑_ : (ℓ ℓ' : L) → Dec (ℓ ⊑ ℓ')

module LatticeEverything (L₀ : Lattice) where    
  open Lattice L₀ public

  _̷⊑_ : L → L → Set
  ℓ₀ ̷⊑ ℓ₁ = ¬ (ℓ₀ ⊑ ℓ₁)

  residuation-⊥ : ∀{ℓ₀ ℓ₁ : L} → ℓ₀ ∶ ℓ₁ ≡ ⊥ → ℓ₀ ⊑ ℓ₁
  residuation-⊥ {ℓ₀} {ℓ₁} refl =
    ⊑-transitive (∶-growing {ℓ₀} {ℓ₁})
    (⊔-least-upper (⊑-transitive (⊑-equality (⊑-antisymmetric ⊥-least (∶-left-move ⊥-least))) (∶-left-move ∶-growing)) ⊑-reflexive)
  
  ⊥-residuation : ∀{ℓ₀ ℓ₁ : L} → ℓ₀ ⊑ ℓ₁ → ℓ₀ ∶ ℓ₁ ≡ ⊥
  ⊥-residuation {ℓ₀} {ℓ₁} x = ⊑-antisymmetric (∶-left-move (⊑-transitive x ⊔-upper-bound)) ⊥-least
  
  residuation-less-than : ∀{ℓ₀ ℓ₁ : L} → (ℓ₀ ∶ ℓ₁) ⊑ ℓ₀
  residuation-less-than {ℓ₀} {ℓ₁} = ∶-left-move (⊑-transitive ⊔-upper-bound (⊑-equality ⊔-commutative))
  
  -- Galois connection
  galois-left-to-right : (ℓ : L) → ∀{ℓ₀ ℓ₁ : L} → (ℓ₀ ∶ ℓ) ⊑ ℓ₁ → ℓ₀ ⊑ (ℓ₁ ⊔ ℓ)
  galois-left-to-right ℓ {ℓ₀} {ℓ₁} x =
    ⊑-transitive (∶-growing {ℓ₀} {ℓ}) (⊔-least-upper (⊑-transitive x ⊔-upper-bound) (⊑-transitive ⊔-upper-bound (⊑-equality ⊔-commutative)))
  
  galois-right-to-left : (ℓ : L) → ∀{ℓ₀ ℓ₁ : L} → ℓ₀ ⊑ (ℓ₁ ⊔ ℓ) → (ℓ₀ ∶ ℓ) ⊑ ℓ₁
  galois-right-to-left ℓ x = ∶-left-move (⊑-transitive x (⊑-equality ⊔-commutative))
  
  _⇔_ : Set → Set → Set
  a ⇔ b = (a → b) × (b → a)
  
  formsGalois : (f g : L → L) → Set
  formsGalois f g = {ℓ₀ ℓ₁ : L} → (f ℓ₀ ⊑ ℓ₁) ⇔ (ℓ₀ ⊑ g ℓ₁)
  
  galois∶⊔ : ∀{ℓ : L} → formsGalois (λ ℓ₀ → ℓ₀ ∶ ℓ) (λ ℓ₀ → ℓ₀ ⊔ ℓ)
  galois∶⊔ {ℓ} = galois-left-to-right ℓ , galois-right-to-left ℓ
  
  is-residuation-wrt-⊔ : (L → L → L) → Set
  is-residuation-wrt-⊔ f = (∀{ℓ ℓ'} → ℓ ⊑ ((f ℓ ℓ') ⊔ ℓ')) × (∀{ℓ ℓ' ℓ''} → ℓ ⊑ (ℓ' ⊔ ℓ'') → (f ℓ ℓ') ⊑ ℓ'')
  
  galois-to-residuation : ∀{f : L → L → L} → (∀{ℓ'} → formsGalois (λ ℓ → f ℓ ℓ') (λ ℓ → ℓ ⊔ ℓ'))
                        → is-residuation-wrt-⊔ f
  galois-to-residuation {f} x = (λ {ℓ} {ℓ'} → proj₁ x ⊑-reflexive) ,
                                 λ {ℓ} {ℓ'} {ℓ''} → λ p → proj₂ x (⊑-transitive p (⊑-equality ⊔-commutative))
  
  -- Replacability
  _replaces_under_ : L → L → L → Set
  ℓ' replaces ℓ₁ under ℓ₀ = ∀{ℓ*} → ℓ₀ ⊑ ℓ* → (ℓ₁ ⊑ ℓ*) ⇔ (ℓ' ⊑ ℓ*)

  residual-replace : ∀{ℓ₀ ℓ₁} → (ℓ₁ ∶ ℓ₀) replaces ℓ₁ under ℓ₀
  residual-replace {ℓ₀} {ℓ₁} x = ⊑-transitive residuation-less-than ,
                               λ p → ⊑-transitive (galois-left-to-right ℓ₀ p) (⊔-least-upper ⊑-reflexive x)
  
  residual-minimal-replace : ∀{ℓ₀ ℓ₁ ℓ₂} → ℓ₂ replaces ℓ₁ under ℓ₀ → (ℓ₁ ∶ ℓ₀) ⊑ ℓ₂
  residual-minimal-replace {ℓ₀} {ℓ₁} {ℓ₂} x with x {ℓ₀ ⊔ ℓ₂} ⊔-upper-bound
  ... | lp , rp = ∶-left-move (rp (⊑-transitive ⊔-upper-bound (⊑-equality ⊔-commutative)))
