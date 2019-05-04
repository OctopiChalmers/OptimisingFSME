module Contexts (Type : Set) where
open import Data.Nat
open import Data.List

Ctx : Set
Ctx = List Type

data _∈_ : Type → Ctx → Set where
  hd : ∀ {t₀ Γ} → t₀ ∈ (t₀ ∷ Γ)
  tl : ∀ {t₀ t₁ Γ} → t₀ ∈ Γ → t₀ ∈ (t₁ ∷ Γ)

∈++ : ∀{x Γ Γ'} → x ∈ Γ → x ∈ (Γ' ++ Γ)
∈++ {Γ' = []} x₁ = x₁
∈++ {Γ' = x ∷ Γ'} x₁ = tl (∈++ x₁)

_⊆_ : Ctx → Ctx → Set
Γ ⊆ Γ' = ∀ {x} → x ∈ Γ → x ∈ Γ'

⊆-cons : ∀{Γ Γ' t} → Γ ⊆ Γ' → (t ∷ Γ) ⊆ (t ∷ Γ')
⊆-cons x hd = hd
⊆-cons x (tl x₁) = tl (x x₁)
