open import Lattices
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty hiding (⊥)
open import Relation.Nullary
module LatticeContexts (L₀ : Lattice) where

open LatticeEverything L₀

data Branch : Set where
  + : L → Branch
  - : L → Branch

Context : Set
Context = List Branch

data _inView_ (ℓ : L) : Context → Set where
  vEmpty    : ℓ inView []
  vPositive : ∀{γ k} → k ⊑ ℓ → ℓ inView γ → ℓ inView (+ k ∷ γ)
  vNegative : ∀{γ k} → k ̷⊑ ℓ → ℓ inView γ → ℓ inView (- k ∷ γ)

positives : Context → List L
positives [] = []
positives (+ x ∷ γ) = x ∷ positives γ
positives (- x ∷ γ) = positives γ

candidate : Context → L
candidate γ = foldr _⊔_ ⊥ (positives γ)

negatives : Context → List L
negatives [] = []
negatives (+ x ∷ pc) = negatives pc
negatives (- x ∷ pc) = x ∷ negatives pc

coherent : Context → Set
coherent γ = ∃[ ℓ ] (ℓ inView γ)

incoherent : Context → Set
incoherent γ = ¬ (coherent γ)

{- Labels relative to contexts -}
-- "ℓ is positively redundant in γ"
_≼_ : L → Context → Set
ℓ ≼ γ = ∀{ℓ' : L} → ℓ' inView γ → ℓ ⊑ ℓ'

candidate-≼ : ∀{γ} → candidate γ ≼ γ
candidate-≼ vEmpty           = ⊥-least
candidate-≼ (vPositive x x₁) = ⊔-least-upper x (candidate-≼ x₁)
candidate-≼ (vNegative x x₁) = candidate-≼ x₁

{- Proof that coherence is equivalent to `candidate γ inView γ` -}
lemma-coherent : ∀{γ}{ℓ₀ ℓ₁ ℓ₂} → ℓ₀ inView γ → ℓ₁ inView γ
               → ℓ₀ ⊑ ℓ₁ → ℓ₂ ⊑ ℓ₁ → (ℓ₂ ⊔ ℓ₀) inView γ
lemma-coherent {[]} {ℓ₀} {ℓ₁} {ℓ₂} x x₁ x₂ x₃ = vEmpty
lemma-coherent {+ x₄ ∷ γ} {ℓ₀} {ℓ₁} {ℓ₂} (vPositive x x₆) (vPositive x₁ x₅) x₂ x₃ =
  vPositive (⊑-transitive x (⊑-transitive ⊔-upper-bound (⊑-equality ⊔-commutative))) (lemma-coherent x₆ x₅ x₂ x₃)
lemma-coherent { - x₄ ∷ γ} {ℓ₀} {ℓ₁} {ℓ₂} (vNegative x x₅) (vNegative x₁ x₆) x₂ x₃ =
  vNegative (λ p → x₁ (⊑-transitive p (⊔-least-upper x₃ x₂))) (lemma-coherent x₅ x₆ x₂ x₃)

coherent-candidate : ∀{γ} → coherent γ → candidate γ inView γ
coherent-candidate {[]} x = vEmpty
coherent-candidate {+ x₁ ∷ γ} (fst , vPositive x snd) =
  vPositive ⊔-upper-bound (lemma-coherent (coherent-candidate (fst , snd)) snd (candidate-≼ snd) x)
coherent-candidate { - x₁ ∷ γ} (fst , vNegative x snd) =
  vNegative (λ p → x (⊑-transitive p (candidate-≼ snd))) (coherent-candidate (fst , snd))

candidate-coherent : ∀{γ} → candidate γ inView γ → coherent γ
candidate-coherent {γ} x = candidate γ , x

≼-from-candidate : ∀{ℓ γ} → ℓ ⊑ candidate γ → ℓ ≼ γ
≼-from-candidate {γ = []} x x₁ = ⊑-transitive x ⊥-least
≼-from-candidate {γ = + x₂ ∷ γ} x (vPositive x₁ x₃) = ⊑-transitive x (⊔-least-upper x₁ (≼-from-candidate ⊑-reflexive x₃))
≼-from-candidate {γ = - x₂ ∷ γ} x (vNegative x₁ x₃) = ≼-from-candidate x x₃

candidate-from-≼ : ∀{ℓ γ} → coherent γ → ℓ ≼ γ → ℓ ⊑ candidate γ
candidate-from-≼ {γ = γ} p q = q (coherent-candidate p)

_/_ : L → Context → Set
ℓ / pc = ∀{ℓ' : L} → ℓ' inView pc → ℓ ̷⊑ ℓ'

{- Replacement under a context -}
_replaces_underContext_ : L → L → Context → Set
ℓ' replaces ℓ underContext γ = ∀ {ℓ*} → ℓ* inView γ → (ℓ ⊑ ℓ*) ⇔ (ℓ' ⊑ ℓ*)

residual-replace-context : ∀{ℓ γ} → (ℓ ∶ candidate γ) replaces ℓ underContext γ
residual-replace-context x = (λ p → ⊑-transitive residuation-less-than p) ,
                             (λ p → ⊑-transitive (proj₁ galois∶⊔ p)
                                       (⊑-equality (⊑-antisymmetric
                                         (⊔-least-upper ⊑-reflexive (candidate-≼ x))
                                       ⊔-upper-bound)))

residual-minimal-replace-context : ∀{ℓ' ℓ γ} → coherent (+ ℓ ∷ γ) → ℓ' replaces ℓ underContext γ → (ℓ ∶ candidate γ) ⊑ ℓ'
residual-minimal-replace-context {ℓ'} {ℓ} {γ} cjoin x with cjoin
... | ℓ₀ , vPositive x₀ x₁ with coherent-candidate (ℓ₀ , vPositive (proj₁ (x x₁) x₀) x₁)
... | vPositive x₁' x₂ = ∶-left-move (⊑-transitive (proj₂ (x x₂) x₁') (⊑-equality ⊔-commutative))
