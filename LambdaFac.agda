open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Empty renaming (⊥ to ⊥⊥)
open import Lattices
open import Data.Product
open import Data.List
open import Data.Sum
open import Data.Nat
import Contexts
module LambdaFac (L₀ : Lattice) where

open Lattice L₀ renaming (⊥ to L⊥)

data Type : Set where
  unit  : Type
  _⇒_   : Type → Type → Type

open Contexts Type

data LE : Set where
  atom : (ℓ : L) → LE
  _∨_  : LE → LE → LE
  _∧_  : LE → LE → LE
  ¬'    : LE → LE

_⊨_ : L → LE → Set
ℓ ⊨ atom ℓ₁ = ℓ₁ ⊑ ℓ
ℓ ⊨ (e ∨ e₁) = (ℓ ⊨ e) ⊎ (ℓ ⊨ e₁)
ℓ ⊨ (e ∧ e₁) = (ℓ ⊨ e) × (ℓ ⊨ e₁)
ℓ ⊨ ¬' e = ¬ (ℓ ⊨ e)

_?⊨_ : (ℓ : L) → (e : LE) → Dec (ℓ ⊨ e)
ℓ ?⊨ atom ℓ₁ = ℓ₁ ?⊑ ℓ
ℓ ?⊨ (e ∨ e₁) with ℓ ?⊨ e
... | yes p = yes (inj₁ p)
ℓ ?⊨ (e ∨ e₁) | no ¬p with ℓ ?⊨ e₁
... | yes q = yes (inj₂ q)
... | no ¬q = no (λ { (inj₁ p) → ¬p p ; (inj₂ q) → ¬q q })
ℓ ?⊨ (e ∧ e₁) with (ℓ ?⊨ e , ℓ ?⊨ e₁)
... | yes p , yes p₁ = yes (p , p₁)
... | yes p , no ¬p = no (λ z → ¬p (proj₂ z))
... | no ¬p , snd = no (λ z → ¬p (proj₁ z))
ℓ ?⊨ ¬' e with ℓ ?⊨ e
... | yes p = no (λ z → z p)
... | no ¬p = yes ¬p

data _⊢_ : Ctx → Type → Set where
  Var            : ∀{Γ t} → t ∈ Γ → Γ ⊢ t
  λ'             : ∀{Γ t₀ t₁} → t₀ ∷ Γ ⊢ t₁ → Γ ⊢ t₀ ⇒ t₁
  _•_            : ∀{Γ t₀ t₁} → Γ ⊢ t₀ ⇒ t₁ → Γ ⊢ t₀ → Γ ⊢ t₁
  <>             : ∀{Γ} → Γ ⊢ unit
  ⟨_*_∶_⟩        : ∀{Γ t} → L → Γ ⊢ t → Γ ⊢ t → Γ ⊢ t
  μ              : ∀{Γ t} → t ∷ Γ ⊢ t → Γ ⊢ t
  ⊥              : ∀{Γ t} → Γ ⊢ t
  _⇓_            : ∀{Γ t} → Γ ⊢ t → LE → Γ ⊢ t

infixl 0 _⊢_

_↓_ : ∀{Γ t} → Γ ⊢ t → L → Γ ⊢ t
Var x ↓ ℓ = Var x
λ' x ↓ ℓ = λ' (x ↓ ℓ)
(x • x₁) ↓ ℓ = (x ↓ ℓ) • (x₁ ↓ ℓ)
<> ↓ ℓ = <>
μ x ↓ ℓ = μ (x ↓ ℓ)
⟨ ℓ₀ * x₁ ∶ x₂ ⟩ ↓ ℓ with ℓ₀ ?⊑ ℓ
... | yes p = x₁ ↓ ℓ
... | no ¬p = x₂ ↓ ℓ
⊥ ↓ ℓ = ⊥
(e ⇓ ℓe) ↓ ℓ with ℓ ?⊨ ℓe
... | yes p = e ↓ ℓ
... | no ¬p = ⊥

⟦_⟧ : ∀{Γ t} → LE → Γ ⊢ t → Γ ⊢ t → Γ ⊢ t
⟦ atom ℓ ⟧ e₀ e₁   = ⟨ ℓ * e₀ ∶ e₁ ⟩
⟦ ℓe ∨ ℓe₁ ⟧ e₀ e₁ = ⟦ ℓe ⟧ e₀ (⟦ ℓe₁ ⟧ e₀ e₁)
⟦ ℓe ∧ ℓe₁ ⟧ e₀ e₁ = ⟦ ℓe ⟧ (⟦ ℓe₁ ⟧ e₀ e₁) e₁
⟦ ¬' ℓe ⟧ e₀ e₁    = ⟦ ℓe ⟧ e₁ e₀

↓-idempotent : ∀{Γ t ℓ}{e : Γ ⊢ t} → (e ↓ ℓ) ≡ ((e ↓ ℓ) ↓ ℓ)
↓-idempotent {Γ} {t} {ℓ} {Var x} = refl
↓-idempotent {Γ} {.(_ ⇒ _)} {ℓ} {λ' e} = cong λ' (↓-idempotent {e = e})
↓-idempotent {Γ} {t} {ℓ} {e • e₁} = cong₂ _•_ (↓-idempotent {e = e}) (↓-idempotent {e = e₁})
↓-idempotent {Γ} {.unit} {ℓ} {<>} = refl
↓-idempotent {Γ} {t} {ℓ} {μ e} = cong μ (↓-idempotent {e = e})
↓-idempotent {Γ} {t} {ℓ} {⟨ ℓ₁ * e ∶ e₁ ⟩} with ℓ₁ ?⊑ ℓ
... | yes p = ↓-idempotent {e = e}
... | no ¬p = ↓-idempotent {e = e₁}
↓-idempotent {Γ} {t} {ℓ} {⊥} = refl
↓-idempotent {Γ} {t} {ℓ} {e ⇓ ℓe} with ℓ ?⊨ ℓe
... | yes p = ↓-idempotent {e = e}
... | no ¬p = refl


↓-idempotent₂ : ∀{Γ t ℓ ℓ'}(e : Γ ⊢ t) → (e ↓ ℓ) ≡ ((e ↓ ℓ) ↓ ℓ')
↓-idempotent₂ {Γ} {t} {ℓ} {ℓ'} (Var x) = refl
↓-idempotent₂ {Γ} {.(_ ⇒ _)} {ℓ} {ℓ'} (λ' e) = cong λ' (↓-idempotent₂ e)
↓-idempotent₂ {Γ} {t} {ℓ} {ℓ'} (e • e₁) = cong₂ _•_ (↓-idempotent₂ e) (↓-idempotent₂ e₁)
↓-idempotent₂ {Γ} {.unit} {ℓ} {ℓ'} <> = refl
↓-idempotent₂ {Γ} {t} {ℓ} {ℓ'} ⟨ x * e ∶ e₁ ⟩ with x ?⊑ ℓ
... | yes p = ↓-idempotent₂ e
... | no ¬p = ↓-idempotent₂ e₁
↓-idempotent₂ {Γ} {t} {ℓ} {ℓ'} (μ e) = cong μ (↓-idempotent₂ e)
↓-idempotent₂ {Γ} {t} {ℓ} {ℓ'} ⊥ = refl
↓-idempotent₂ {Γ} {t} {ℓ} {ℓ'} (e ⇓ x) with ℓ ?⊨ x
... | yes p = ↓-idempotent₂ e
... | no ¬p = refl

_~⟨_⟩_ : ∀{Γ t} → Γ ⊢ t → L → Γ ⊢ t → Set
e ~⟨ ℓ ⟩ e' = (e ↓ ℓ) ≡ (e' ↓ ℓ)

weaken : ∀{Γ Γ' t} → Γ ⊆ Γ' → Γ ⊢ t → Γ' ⊢ t
weaken x (Var x₁) = Var (x x₁)
weaken x (λ' x₁) = λ' (weaken (⊆-cons x) x₁)
weaken x (x₁ • x₂) = weaken x x₁ • weaken x x₂
weaken x (μ x₁) = μ (weaken (⊆-cons x) x₁)
weaken x <> = <>
weaken x ⟨ ℓ * x₂ ∶ x₃ ⟩ = ⟨ ℓ * weaken x x₂ ∶ weaken x x₃ ⟩
weaken x ⊥ = ⊥
weaken x (e ⇓ ℓ) = (weaken x e) ⇓ ℓ

weaken-↓ : ∀{Γ Γ' t ℓ*} → (p : Γ ⊆ Γ') → (e : Γ ⊢ t) → weaken p (e ↓ ℓ*) ≡ weaken p e ↓ ℓ*
weaken-↓ p (Var x) = refl
weaken-↓ p (λ' e) = cong λ' (weaken-↓ (⊆-cons p) e)
weaken-↓ p (e • e₁) = cong₂ _•_ (weaken-↓ p e) (weaken-↓ p e₁)
weaken-↓ p <> = refl
weaken-↓ p (μ e) = cong μ (weaken-↓ (⊆-cons p) e)
weaken-↓ {ℓ* = ℓ*} p ⟨ ℓ * e ∶ e₁ ⟩ with ℓ ?⊑ ℓ*
... | yes q = weaken-↓ p e
... | no ¬q = weaken-↓ p e₁
weaken-↓ p ⊥ = refl
weaken-↓ {ℓ* = ℓ*} p (e ⇓ ℓe) with ℓ* ?⊨ ℓe
... | yes q = weaken-↓ p e
... | no ¬q = refl

var-subst : ∀{s t} (Γ Γ' : Ctx)
   → Γ' ⊢ s
   → t ∈ (Γ ++ [ s ] ++ Γ') 
   → (Γ ++ Γ') ⊢ t
var-subst [] Γ' x hd = x
var-subst [] Γ' x (tl x₁) = Var x₁
var-subst (x₂ ∷ Γ) Γ' x hd = Var hd
var-subst (x₂ ∷ Γ) Γ' x (tl x₁) = weaken tl (var-subst Γ Γ' x x₁)

var-subst-↓ : ∀{s t ℓ*}
            → (Γ Γ' : Ctx)
            → (e : Γ' ⊢ s)
            → (p : t ∈ (Γ ++ [ s ] ++ Γ'))
            → var-subst Γ Γ' e p ↓ ℓ* ≡ var-subst Γ Γ' (e ↓ ℓ*) p
var-subst-↓ [] Γ' e hd = refl
var-subst-↓ [] Γ' e (tl p) = refl
var-subst-↓ {ℓ* = ℓ*} (x ∷ Γ) Γ' e hd = refl
var-subst-↓ {ℓ* = ℓ*} (x ∷ Γ) Γ' e (tl p) =
  let ih = var-subst-↓ {ℓ* = ℓ*} Γ Γ' e p in
  let hlp = sym (weaken-↓ {ℓ* = ℓ*} tl (var-subst Γ Γ' e p)) in
  trans hlp (cong (weaken tl) ih)

tm-subst : ∀{s t} (Γ Γ' : Ctx) 
   → Γ' ⊢ s
   → (Γ ++ [ s ] ++ Γ') ⊢ t
   → (Γ ++ Γ') ⊢ t 
tm-subst Γ Γ' x (Var x₁) = var-subst Γ Γ' x x₁
tm-subst Γ Γ' x (λ' {t₀ = t₀} x₁) = λ' (tm-subst (t₀ ∷ Γ) Γ' x x₁)
tm-subst Γ Γ' x (x₁ • x₂) = tm-subst Γ Γ' x x₁ • tm-subst Γ Γ' x x₂
tm-subst Γ Γ' x <> = <>
tm-subst Γ Γ' x (μ {t = t} x₁) = μ (tm-subst (t ∷ Γ) Γ' x x₁)
tm-subst Γ Γ' x ⟨ ℓ * e₀ ∶ e₁ ⟩ = ⟨ ℓ * tm-subst Γ Γ' x e₀ ∶ tm-subst Γ Γ' x e₁ ⟩
tm-subst Γ Γ' x ⊥ = ⊥
tm-subst Γ Γ' x (e ⇓ ℓ) = (tm-subst Γ Γ' x e) ⇓ ℓ

tm-subst-↓ : ∀{s t ℓ*}
           → (Γ Γ' : Ctx) 
           → (e : Γ' ⊢ s)
           → (e' : (Γ ++ [ s ] ++ Γ') ⊢ t)
           → tm-subst Γ Γ' e e' ↓ ℓ* ≡ tm-subst Γ Γ' (e ↓ ℓ*) (e' ↓ ℓ*)
tm-subst-↓ Γ Γ' e (Var x) = var-subst-↓ Γ Γ' e x
tm-subst-↓ Γ Γ' e (λ' e') = cong λ' (tm-subst-↓ (_ ∷ Γ) Γ' e e')
tm-subst-↓ Γ Γ' e (e' • e'') = cong₂ _•_ (tm-subst-↓ Γ Γ' e e') (tm-subst-↓ Γ Γ' e e'')
tm-subst-↓ Γ Γ' e <> = refl
tm-subst-↓ Γ Γ' e (μ e') = cong μ (tm-subst-↓ (_ ∷ Γ) Γ' e e')
tm-subst-↓ {ℓ* = ℓ*} Γ Γ' e ⟨ ℓ * e' ∶ e'' ⟩ with ℓ ?⊑ ℓ*
... | yes p = tm-subst-↓ Γ Γ' e e'
... | no ¬p = tm-subst-↓ Γ Γ' e e''
tm-subst-↓ Γ Γ' e ⊥ = refl
tm-subst-↓ {ℓ* = ℓ*} Γ Γ' x (e ⇓ ℓe) with ℓ* ?⊨ ℓe
... | yes p = tm-subst-↓ Γ Γ' x e
... | no ¬p = refl

_/_ : ∀{Γ t s} → (t ∷ Γ) ⊢ s → Γ ⊢ t → Γ ⊢ s
e₀ / e₁ = tm-subst [] _ e₁ e₀

-- Standard semantics
data _⟶s_ : ∀{Γ t} → Γ ⊢ t → Γ ⊢ t → Set where
  AppCs : ∀{Γ t₀ t₁}{e₀ e₀' : Γ ⊢ t₀ ⇒ t₁}{e₁ : Γ ⊢ t₀}
        → e₀ ⟶s e₀'
        -----------------------------------------------
        → (e₀ • e₁) ⟶s (e₀' • e₁)

  AppRs : ∀{Γ t₀ t₁}{e₀ : t₀ ∷ Γ ⊢ t₁}{e₁ : Γ ⊢ t₀}
        -------------------------------------------
        → ((λ' e₀) • e₁) ⟶s (e₀ / e₁)

  Recs  : ∀{Γ t}{e : t ∷ Γ ⊢ t}
        -----------------------
        → μ e ⟶s (e / μ e)

  FacEs : ∀{Γ t ℓ}{e₀ e₀' e₁ : Γ ⊢ t}
        -----------------------------
        → ⟨ ℓ * e₀ ∶ e₁ ⟩ ⟶s e₀

  ⊥Apps : ∀{Γ t₀ t₁}{e : Γ ⊢ t₀}
        ------------------------
        → (⊥ {t = t₀ ⇒ t₁} • e) ⟶s ⊥

  ⇓igns : ∀{Γ t ℓe}{e : Γ ⊢ t}
        -------------------
        → (e ⇓ ℓe) ⟶s e

data StdValue : ∀{Γ t} → Γ ⊢ t → Set where
  SVLam  : ∀{Γ t₀ t₁}{e : t₀ ∷ Γ ⊢ t₁} → StdValue (λ' e)
  SVUnit : ∀{Γ} → StdValue (<> {Γ})

-- Faceted semantics
data _⟶f_ : ∀{Γ t} → Γ ⊢ t → Γ ⊢ t → Set where
  AppCf  : ∀{Γ t₀ t₁}{e₀ e₀' : Γ ⊢ t₀ ⇒ t₁}{e₁ : Γ ⊢ t₀}
         → e₀ ⟶f e₀'
         -----------------------------------------------
         → (e₀ • e₁) ⟶f (e₀' • e₁)

  AppRf  : ∀{Γ t₀ t₁}{e₀ : t₀ ∷ Γ ⊢ t₁}{e₁ : Γ ⊢ t₀}
         -------------------------------------------
         → ((λ' e₀) • e₁) ⟶f (e₀ / e₁)

  Recf   : ∀{Γ t}{e : t ∷ Γ ⊢ t}
         -----------------------
         → μ e ⟶f (e / μ e)

  AppFf  : ∀{Γ t₀ t₁ ℓ}{e₀ e₁ : Γ ⊢ t₀ ⇒ t₁}{e₂ : Γ ⊢ t₀}
         -----------------------------------------------------
         → (⟨ ℓ * e₀ ∶ e₁ ⟩ • e₂) ⟶f ⟨ ℓ * e₀ • e₂ ∶ e₁ • e₂ ⟩

  FacCLf : ∀{Γ t ℓ}{e₀ e₀' e₁ : Γ ⊢ t}
         → e₀ ⟶f e₀'
         -------------------------------------
         → ⟨ ℓ * e₀ ∶ e₁ ⟩ ⟶f ⟨ ℓ * e₀' ∶ e₁ ⟩

  FacCRf : ∀{Γ t ℓ}{e₀ e₁ e₁' : Γ ⊢ t}
         → e₁ ⟶f e₁'
         -------------------------------------
         → ⟨ ℓ * e₀ ∶ e₁ ⟩ ⟶f ⟨ ℓ * e₀ ∶ e₁' ⟩

  Optf   : ∀{Γ t}{e₀ e₁ : Γ ⊢ t}
         → (∀(ℓ : L) → e₀ ~⟨ ℓ ⟩ e₁)
         ---------------------------
         → e₀ ⟶f e₁
  
  ⊥Appf  : ∀{Γ t₀ t₁}{e : Γ ⊢ t₀}
         ------------------------
         → (⊥ {t = t₀ ⇒ t₁} • e) ⟶f ⊥

  ⇓expf  : ∀{Γ t ℓe}{e : Γ ⊢ t}
         -------------------
         → (e ⇓ ℓe) ⟶f ⟦ ℓe ⟧ e ⊥

data _⟶f*_ {Γ t} : Γ ⊢ t → Γ ⊢ t → Set where
  ref  : ∀{e : Γ ⊢ t} → e ⟶f* e
  _﹔_ : ∀{e e' e'' : Γ ⊢ t} → e ⟶f e' → e' ⟶f* e'' → e ⟶f* e''

data _⟶s*_ {Γ t} : Γ ⊢ t → Γ ⊢ t → Set where
  ref  : ∀{e : Γ ⊢ t} → e ⟶s* e
  _﹔_ : ∀{e e' e'' : Γ ⊢ t} → e ⟶s e' → e' ⟶s* e'' → e ⟶s* e''

congruence : ∀{Γ t t'} → (c : (Γ ⊢ t) → Γ ⊢ t')
           → (∀{e e' : Γ ⊢ t} → e ⟶f e' → c e ⟶f c e')
           → (e e' : Γ ⊢ t)
           → e ⟶f* e'
           → c e ⟶f* c e'
congruence c x e .e ref = ref
congruence c x e e' (x₁ ﹔ x₂) = (x x₁) ﹔ (congruence c x _ _ x₂)

↓⊑ : ∀{ℓ ℓ' Γ t}{e₀ e₁ : Γ ⊢ t} → ℓ ⊑ ℓ' → (⟨ ℓ * e₀ ∶ e₁ ⟩ ↓ ℓ') ≡ (e₀ ↓ ℓ')
↓⊑ {ℓ} {ℓ'} x with ℓ ?⊑ ℓ'
... | yes p = refl
... | no ¬p = ⊥-elim (¬p x)

mutual
  ↓⊨ : ∀{ℓ ℓe Γ t}{e₀ e₁ : Γ ⊢ t} → ℓ ⊨ ℓe → (⟦ ℓe ⟧ e₀ e₁ ↓ ℓ) ≡ (e₀ ↓ ℓ)
  ↓⊨ {ℓ} {atom ℓ₁} x with ℓ₁ ?⊑ ℓ
  ... | yes p = refl
  ... | no ¬p = ⊥-elim (¬p x)
  ↓⊨ {ℓ} {ℓe ∨ ℓe₁} (inj₁ x) = ↓⊨ {ℓe = ℓe} x
  ↓⊨ {ℓ} {ℓe ∨ ℓe₁} (inj₂ y) with ℓ ?⊨ ℓe
  ... | yes p = ↓⊨ {ℓe = ℓe} p
  ... | no ¬p = trans (↓¬⊨ {ℓe = ℓe} ¬p) (↓⊨ {ℓe = ℓe₁} y)
  ↓⊨ {ℓ} {ℓe ∧ ℓe₁} {e₀ = e₀} {e₁} x = trans (↓⊨ {ℓe = ℓe} {e₀ = ⟦ ℓe₁ ⟧ e₀ e₁} {e₁ = e₁} (proj₁ x))
                                             (↓⊨ {ℓe = ℓe₁} {e₀ = e₀} {e₁ = e₁} (proj₂ x))
  ↓⊨ {ℓ} {¬' ℓe} {e₀ = e₀} {e₁ = e₁} x with ℓ ?⊨ ℓe
  ... | yes p = ⊥-elim (x p)
  ... | no ¬p = ↓¬⊨ {ℓ} {ℓe} {e₀ = e₁} {e₁ = e₀} ¬p

  ↓¬⊨ : ∀{ℓ ℓe Γ t}{e₀ e₁ : Γ ⊢ t} → ¬ (ℓ ⊨ ℓe) → (⟦ ℓe ⟧ e₀ e₁ ↓ ℓ) ≡ (e₁ ↓ ℓ)
  ↓¬⊨ {ℓ₁} {atom ℓ} x with ℓ ?⊑ ℓ₁
  ... | yes p = ⊥-elim (x p)
  ... | no ¬p = refl
  ↓¬⊨ {ℓ} {ℓe = ℓe ∨ ℓe₁} x with (ℓ ?⊨ ℓe , ℓ ?⊨ ℓe₁)
  ↓¬⊨ {ℓ} {ℓe ∨ ℓe₁} x | yes p , snd = ⊥-elim (x (inj₁ p))
  ↓¬⊨ {ℓ} {ℓe ∨ ℓe₁} x | no ¬p , yes p = ⊥-elim (x (inj₂ p))
  ↓¬⊨ {ℓ} {ℓe ∨ ℓe₁} x | no ¬p , no ¬p₁ = trans (↓¬⊨ {ℓe = ℓe} ¬p) (↓¬⊨ {ℓe = ℓe₁} ¬p₁)
  ↓¬⊨ {ℓ} {ℓe ∧ ℓe₁} x with (ℓ ?⊨ ℓe , ℓ ?⊨ ℓe₁)
  ↓¬⊨ {ℓ} {ℓe ∧ ℓe₁} x | yes p , yes p₁ = ⊥-elim (x (p , p₁))
  ↓¬⊨ {ℓ} {ℓe ∧ ℓe₁} x | yes p , no ¬p = trans (↓⊨ {ℓe = ℓe} p) (↓¬⊨ {ℓe = ℓe₁} ¬p)
  ↓¬⊨ {ℓ} {ℓe ∧ ℓe₁} x | no ¬p , snd = ↓¬⊨ {ℓe = ℓe} ¬p
  ↓¬⊨ {ℓ} {¬' ℓe} x with ℓ ?⊨ ℓe
  ... | yes p = ↓⊨ {ℓe = ℓe} p
  ... | no ¬p = ⊥-elim (x ¬p)

↓¬⊑ : ∀{ℓ ℓ' Γ t}{e₀ e₁ : Γ ⊢ t} → ¬ (ℓ ⊑ ℓ') → (⟨ ℓ * e₀ ∶ e₁ ⟩ ↓ ℓ') ≡ (e₁ ↓ ℓ')
↓¬⊑ {ℓ} {ℓ'} x with ℓ ?⊑ ℓ'
... | yes p = ⊥-elim (x p)
... | no ¬p = refl

⟶f*++ : ∀{Γ t} → {e e' e'' : Γ ⊢ t} → e ⟶f* e' → e' ⟶f* e'' → e ⟶f* e''
⟶f*++ ref x₁ = x₁
⟶f*++ (x ﹔ x₂) x₁ = x ﹔ ⟶f*++ x₂ x₁

⟦⟧-cong : ∀{Γ t} → (e₀ e₁ e₀' e₁' : Γ ⊢ t) → (ℓe : LE) → e₀ ⟶f* e₀' → e₁ ⟶f* e₁' → (⟦ ℓe ⟧ e₀ e₁) ⟶f* (⟦ ℓe ⟧ e₀' e₁')
⟦⟧-cong e₀ e₁ e₀' e₁' (atom ℓ) x x₁ = ⟶f*++ (congruence (λ z → ⟨ ℓ * z ∶ e₁ ⟩) FacCLf e₀ e₀' x) (congruence (⟨_*_∶_⟩ ℓ e₀') FacCRf e₁ e₁' x₁)
⟦⟧-cong e₀ e₁ e₀' e₁' (ℓe ∨ ℓe₁) x x₁ = ⟦⟧-cong e₀ (⟦ ℓe₁ ⟧ e₀ e₁) e₀' (⟦ ℓe₁ ⟧ e₀' e₁') ℓe x (⟦⟧-cong e₀ e₁ e₀' e₁' ℓe₁ x x₁)
⟦⟧-cong e₀ e₁ e₀' e₁' (ℓe ∧ ℓe₁) x x₁ = ⟦⟧-cong (⟦ ℓe₁ ⟧ e₀ e₁) e₁ (⟦ ℓe₁ ⟧ e₀' e₁') e₁' ℓe (⟦⟧-cong e₀ e₁ e₀' e₁' ℓe₁ x x₁) x₁
⟦⟧-cong e₀ e₁ e₀' e₁' (¬' ℓe) x x₁ = ⟦⟧-cong e₁ e₀ e₁' e₀' ℓe x₁ x

applicationLifting : ∀{Γ t₀ t₁} → (e₀ e₁ : Γ ⊢ t₀ ⇒ t₁) → (e₂ : Γ ⊢ t₀) → (ℓe : LE)
                   → ((⟦ ℓe ⟧ e₀ e₁) • e₂) ⟶f* (⟦ ℓe ⟧ (e₀ • e₂) (e₁ • e₂))
applicationLifting e₀ e₁ e₂ (atom ℓ) = AppFf ﹔ ref
applicationLifting e₀ e₁ e₂ (ℓe ∨ ℓe₁) =
  ⟶f*++ (applicationLifting e₀ (⟦ ℓe₁ ⟧ e₀ e₁) e₂ ℓe)
        (⟦⟧-cong (e₀ • e₂) (⟦ ℓe₁ ⟧ e₀ e₁ • e₂) (e₀ • e₂) (⟦ ℓe₁ ⟧ (e₀ • e₂) (e₁ • e₂)) ℓe ref (applicationLifting e₀ e₁ e₂ ℓe₁))
applicationLifting e₀ e₁ e₂ (ℓe ∧ ℓe₁) =
  ⟶f*++ (applicationLifting (⟦ ℓe₁ ⟧ e₀ e₁) e₁ e₂ ℓe)
        (⟦⟧-cong (⟦ ℓe₁ ⟧ e₀ e₁ • e₂) (e₁ • e₂) (⟦ ℓe₁ ⟧ (e₀ • e₂) (e₁ • e₂)) (e₁ • e₂) ℓe (applicationLifting e₀ e₁ e₂ ℓe₁) ref)
applicationLifting e₀ e₁ e₂ (¬' ℓe) = applicationLifting e₁ e₀ e₂ ℓe

simulation : ∀{Γ t ℓ} → (e e' : Γ ⊢ t) → (e ↓ ℓ) ⟶s e'
           → ∃[ e'' ] (e ⟶f* e'' × e'' ~⟨ ℓ ⟩ e')
simulation (Var x₁) e' ()
simulation (λ' e) e' ()
simulation (Var x₁ • e₁) .(_ • (e₁ ↓ _)) (AppCs ())
simulation (λ' e • e₁) .(_ • (e₁ ↓ _)) (AppCs ())
simulation {ℓ = ℓ} (λ' e • e₁) _ AppRs = (e / e₁) , (AppRf ﹔ ref) ,
  trans (↓-idempotent {e = e / e₁}) (cong (λ e₂ → e₂ ↓ ℓ) (tm-subst-↓ _ _ e₁ e)) 
simulation ((e • e₂) • e₁) .(_ • (e₁ ↓ _)) (AppCs {e₀' = e₀} x) with simulation (e • e₂) _ x
... | tm , red , pr =
  (tm • e₁) , congruence (λ e₃ → e₃ • e₁) AppCf (e • e₂) tm red , cong₂ _•_ pr (↓-idempotent {e = e₁})
simulation {ℓ = ℓ} (⟨ ℓ₁ * e ∶ e₂ ⟩ • e₁) e' x with ℓ₁ ?⊑ ℓ
simulation {ℓ = ℓ} (⟨ ℓ₁ * e ∶ e₂ ⟩ • e₁) e' x | yes p with simulation (e • e₁) e' x
... | tm , red , pr = ⟨ ℓ₁ * tm ∶ e₂ • e₁ ⟩ , (AppFf ﹔ congruence (λ e₃ → ⟨ ℓ₁ * e₃ ∶ e₂ • e₁ ⟩) FacCLf (e • e₁) tm red) , trans (↓⊑ p) pr
simulation {ℓ = ℓ} (⟨ ℓ₁ * e ∶ e₂ ⟩ • e₁) e' x | no ¬p with simulation (e₂ • e₁) e' x
... | tm , red , pr = ⟨ ℓ₁ * e • e₁ ∶ tm ⟩ , (AppFf ﹔ congruence (λ e₃ → ⟨ ℓ₁ * e • e₁ ∶ e₃ ⟩) FacCRf (e₂ • e₁) tm red) , trans (↓¬⊑ ¬p) pr
simulation (⊥ • e) .(_ • (e ↓ _)) (AppCs ())
simulation (⊥ {t = t₀ ⇒ t₁} • e) (⊥ {Γ} {t₁}) ⊥Apps = ⊥ , (⊥Appf ﹔ ref) , refl
simulation <> e' ()
simulation {ℓ = ℓ} ⟨ ℓ₁ * e ∶ e₁ ⟩ e' x with ℓ₁ ?⊑ ℓ
simulation {ℓ = ℓ} ⟨ ℓ₁ * e ∶ e₁ ⟩ e' x | yes p with simulation {ℓ = ℓ} e e' x
... | tm , red , pr = ⟨ ℓ₁ * tm ∶ e₁ ⟩ , congruence (λ e₂ → ⟨ ℓ₁ * e₂ ∶ e₁ ⟩) FacCLf e tm red , trans (↓⊑ p) pr
simulation {ℓ = ℓ} ⟨ ℓ₁ * e ∶ e₁ ⟩ e' x | no ¬p with simulation {ℓ = ℓ} e₁ e' x
... | tm , red , pr = ⟨ ℓ₁ * e ∶ tm ⟩ , congruence (λ e₂ → ⟨ ℓ₁ * e ∶ e₂ ⟩) FacCRf e₁ tm red , trans (↓¬⊑ ¬p) pr
simulation (μ {t = .(_ ⇒ _)} e • e₁) .(e₀' • (e₁ ↓ _)) (AppCs {e₀' = e₀'} x) with simulation (μ e) e₀' x
... | tm , red , pr =
  (tm • e₁) , congruence (λ e₂ → e₂ • e₁) AppCf (μ e) tm red , trans (cong₂ _•_ pr refl) (cong₂ _•_ refl (↓-idempotent {e = e₁}))
simulation (μ e) .(tm-subst [] _ (μ (e ↓ _)) (e ↓ _)) Recs =
  (e / μ e) , (Recf ﹔ ref) , trans (tm-subst-↓ _ _ (μ e) e)
                                    (sym (trans (tm-subst-↓ _ _ (μ (e ↓ _)) (e ↓ _))
                                    (sym (cong₂ _/_ (↓-idempotent {e = e}) (↓-idempotent {e = μ e})))))
simulation ⊥ _ ()
simulation {ℓ = ℓ} (_⇓_ {t = .(_ ⇒ _)} e x • e₁) e' x₁ with ℓ ?⊨ x
... | yes p =
  let tm , red , eq = simulation (e • e₁) e' x₁ in
  ⟦ x ⟧ tm ⊥ ,
  (AppCf ⇓expf ﹔ ⟶f*++ (applicationLifting e ⊥ e₁ x) (⟦⟧-cong (e • e₁) (⊥ • e₁) tm ⊥ x red (⊥Appf ﹔ ref))) ,
  trans (↓⊨ {ℓe = x} p) eq
simulation {ℓ = ℓ} (_⇓_ {_} {.(_ ⇒ _)} e x • e₁) .(_ • (e₁ ↓ ℓ)) (AppCs ()) | no ¬p
simulation {ℓ = ℓ} (_⇓_ {_} {.(_ ⇒ _)} e x • e₁) .⊥ ⊥Apps | no ¬p =
  ⟦ x ⟧ (e • e₁) ⊥ ,
  (AppCf ⇓expf ﹔ ⟶f*++ (applicationLifting e ⊥ e₁ x) (⟦⟧-cong (e • e₁) (⊥ • e₁) (e • e₁) ⊥ x ref (⊥Appf ﹔ ref))) ,
  ↓¬⊨ {ℓe = x} ¬p
simulation {ℓ = ℓ} (e ⇓ x) e' x₁ with ℓ ?⊨ x
... | yes p =
  let tm , red , eq = simulation e e' x₁ in
  ⟦ x  ⟧ tm ⊥ , (⇓expf ﹔ ⟦⟧-cong e ⊥ tm ⊥ x red ref) , trans (↓⊨ {ℓe = x} {e₀ = tm} {e₁ = ⊥} p) eq
simulation {ℓ = ℓ} (e ⇓ x) e' () | no ¬p

↓-standard : ∀{Γ t ℓ} → (e e' : Γ ⊢ t) → (e ↓ ℓ) ⟶s e'
           → e' ≡ (e' ↓ ℓ)
↓-standard (Var x₁) e' ()
↓-standard (λ' e) e' ()
↓-standard (Var x₁ • e₁) .(_ • (e₁ ↓ _)) (AppCs ())
↓-standard (λ' e • e₁) .(_ • (e₁ ↓ _)) (AppCs ())
↓-standard (λ' e • e₁) .(tm-subst [] _ (e₁ ↓ _) (e ↓ _)) AppRs =
  trans (sym (tm-subst-↓ _ _ e₁ e)) (trans (↓-idempotent {e = e / e₁}) (cong (λ e₂ → e₂ ↓ _) (tm-subst-↓ _ _ e₁ e)))
↓-standard ((e • e₂) • e₁) .(_ • (e₁ ↓ _)) (AppCs x) = cong₂ _•_ (↓-standard (e • e₂) _ x) (↓-idempotent {e = e₁})
↓-standard {ℓ = ℓ} (⟨ ℓ₁ * e ∶ e₂ ⟩ • e₁) e' x with ℓ₁ ?⊑ ℓ
... | yes p = ↓-standard (e • e₁) e' x
... | no ¬p = ↓-standard (e₂ • e₁) e' x
↓-standard <> e' ()
↓-standard {ℓ = ℓ} ⟨ ℓ₁ * e ∶ e₁ ⟩ e' x with ℓ₁ ?⊑ ℓ
... | yes p = ↓-standard e e' x
... | no ¬p = ↓-standard e₁ e' x
↓-standard (⊥ • e) e' (AppCs ())
↓-standard (⊥ {t = t₀ ⇒ t₁} • e) (⊥ {Γ} {t₁}) ⊥Apps = refl
↓-standard (μ {t = .(_ ⇒ _)} e • e₁) .(_ • (e₁ ↓ _)) (AppCs x) = cong₂ _•_ (↓-standard (μ e) _ x) (↓-idempotent {e = e₁})
↓-standard {ℓ = ℓ} (μ e) .(tm-subst [] _ (μ (e ↓ _)) (e ↓ _)) Recs =
  sym (trans (tm-subst-↓ _ _ (μ (e ↓ ℓ)) (e ↓ ℓ)) (sym (cong₂ _/_ (↓-idempotent {e = e}) (↓-idempotent {e = μ e}))))
↓-standard ⊥ _ ()
↓-standard {ℓ = ℓ} (_⇓_ {t = .(_ ⇒ _)} e x • e₁) e' x₁ with ℓ ?⊨ x
... | yes p = ↓-standard (e • e₁) e' x₁
↓-standard {ℓ = ℓ} (_⇓_ {_} {.(_ ⇒ _)} e x • e₁) .(_ • (e₁ ↓ ℓ)) (AppCs ()) | no ¬p
↓-standard {ℓ = ℓ} (_⇓_ {_} {.(_ ⇒ _)} e x • e₁) .⊥ ⊥Apps | no ¬p = refl
↓-standard {ℓ = ℓ} (e ⇓ x) e' x₁ with ℓ ?⊨ x
... | yes p = ↓-standard e e' x₁
↓-standard {ℓ = ℓ} (e ⇓ x) e' () | no ¬p

coerce : ∀{A B : Set} → A ≡ B → A → B
coerce refl a = a

projection : ∀{Γ t ℓ}
           → (e e' : Γ ⊢ t)
           → e ⟶f e'
           → (e ↓ ℓ) ⟶s (e' ↓ ℓ) ⊎ e ~⟨ ℓ ⟩ e'
projection .(_ • _) .(_ • _) (AppCf x) with projection _ _ x
projection .(_ • _) .(_ • _) (AppCf x) | inj₁ x₁ = inj₁ (AppCs x₁)
projection .(_ • _) .(_ • _) (AppCf x) | inj₂ y = inj₂ (cong₂ _•_ y refl)
projection .(λ' e₀ • e₁) _ (AppRf {e₀ = e₀} {e₁}) = inj₁ (coerce (cong₂ _⟶s_ refl (sym (tm-subst-↓ _ _ e₁ e₀))) AppRs)
projection {ℓ = ℓ₁} .(⟨ ℓ * _ ∶ _ ⟩ • _) .(⟨ ℓ * _ • _ ∶ _ • _ ⟩) (AppFf {ℓ = ℓ}) with ℓ ?⊑ ℓ₁
... | yes p = inj₂ refl
... | no ¬p = inj₂ refl
projection {ℓ = ℓ₁} .(⟨ ℓ * _ ∶ _ ⟩) .(⟨ ℓ * _ ∶ _ ⟩) (FacCLf {ℓ = ℓ} x) with ℓ ?⊑ ℓ₁
... | yes p = projection _ _ x
... | no ¬p = inj₂ refl
projection {ℓ = ℓ₁} .(⟨ ℓ * _ ∶ _ ⟩) .(⟨ ℓ * _ ∶ _ ⟩) (FacCRf {ℓ = ℓ} x) with ℓ ?⊑ ℓ₁
... | yes p = inj₂ refl
... | no ¬p = projection _ _ x
projection _ _ (Optf p) = inj₂ (p _)
projection {ℓ = ℓ} (μ {Γ} {t} e) .(tm-subst [] Γ (μ e) e) Recf =
  inj₁ (coerce (cong₂ _⟶s_ refl (sym (tm-subst-↓ _ _ (μ e) e))) (Recs {e = (e ↓ ℓ)}))
projection (_•_ {Γ} {t₀} {t} (⊥ {Γ} {t₀ ⇒ t}) e) (⊥ {Γ} {t}) ⊥Appf = inj₁ ⊥Apps
projection {ℓ = ℓ} (_⇓_ {Γ} {t} e ℓe) .(⟦ ℓe ⟧ e ⊥) ⇓expf with ℓ ?⊨ ℓe
... | yes p = inj₂ (sym (↓⊨ {ℓe = ℓe} p))
... | no ¬p = inj₂ (sym (↓¬⊨ {ℓe = ℓe} ¬p))

data _clears_ (ℓ : L) : ∀{Γ t} → Γ ⊢ t → Set where
  CVar : ∀{Γ t} → (p : t ∈ Γ) → ℓ clears Var p 

  Cλ'  : ∀{Γ t₀ t₁} → (e : t₀ ∷ Γ ⊢ t₁)
       → ℓ clears e
       → ℓ clears λ' e

  C•   : ∀{Γ t₀ t₁} → (e₀ : Γ ⊢ t₀ ⇒ t₁) → (e₁ : Γ ⊢ t₀)
       → ℓ clears e₀
       → ℓ clears e₁
       → ℓ clears (e₀ • e₁)

  C<>  : ∀{Γ} → ℓ clears (<> {Γ = Γ})

  Cμ   : ∀{Γ t} → (e : t ∷ Γ ⊢ t)
       → ℓ clears e
       → ℓ clears (μ e)

  C⊥   : ∀{Γ t}
       → ℓ clears (⊥ {Γ = Γ} {t = t})

  C⇓   : ∀{Γ t} → (e : Γ ⊢ t) → (ℓe : LE)
       → ℓ ⊨ ℓe
       → ℓ clears e
       → ℓ clears (e ⇓ ℓe)

  Cf  : ∀{Γ t} → (e₀ e₁ : Γ ⊢ t) → (ℓ' : L)
      → ℓ' ⊑ ℓ
      → ℓ clears e₀
      → ℓ clears ⟨ ℓ * e₀ ∶ e₁ ⟩

clearing-simulation : ∀{Γ t ℓ} → (e e' : Γ ⊢ t) → ℓ clears e → e ⟶s e'
                    → ∃[ e'' ] (e ⟶f* e'' × e'' ~⟨ ℓ ⟩ e')
clearing-simulation .(Var p) e' (CVar p) ()
clearing-simulation .(λ' e) e' (Cλ' e x) ()
clearing-simulation .(e₀ • e₁) .(_ • e₁) (C• e₀ e₁ x x₂) (AppCs {e₀' = e₀'} x₁) =
  let tm , red , pr = clearing-simulation e₀ _ x x₁ in
  (tm • e₁) , congruence (λ z → z • e₁) AppCf e₀ tm red , cong₂ _•_ pr refl
clearing-simulation {Γ} .(λ' _ • e₁) _ (C• .(λ' _) e₁ x x₂) (AppRs {e₀ = e₀}) = _ , (AppRf ﹔ ref) , refl
clearing-simulation .(⊥ • e₁) .⊥ (C• .⊥ e₁ x x₂) ⊥Apps = ⊥ , (⊥Appf ﹔ ref) , refl
clearing-simulation .<> e' C<> ()
clearing-simulation .(μ e) .(tm-subst [] _ (μ e) e) (Cμ e x) Recs = (tm-subst [] _ (μ e) e) , (Recf ﹔ ref) , refl
clearing-simulation .⊥ e' C⊥ ()
clearing-simulation .(e ⇓ ℓe) .e (C⇓ e ℓe x x₂) ⇓igns = ⟦ ℓe ⟧ e ⊥ , (⇓expf ﹔ ref) , ↓⊨ {ℓe = ℓe} x
clearing-simulation (⟨_*_∶_⟩ {Γ} {t} ℓ e₂ e₃) .e₂ (Cf e₂ e₃ ℓ' x x₁) FacEs = ⟨ ℓ * e₂ ∶ e₃ ⟩ , ref , ↓⊑ ⊑-reflexive

weaken-clearing : ∀{Γ Γ' t ℓ*} → (p : Γ ⊆ Γ') → (e : Γ ⊢ t) → ℓ* clears e → ℓ* clears weaken p e
weaken-clearing p .(Var p₁) (CVar p₁) = CVar (p p₁)
weaken-clearing p .(λ' e) (Cλ' e x) = Cλ' (weaken (⊆-cons p) e) (weaken-clearing (⊆-cons p) e x)
weaken-clearing p .(e₀ • e₁) (C• e₀ e₁ x x₁) = C• (weaken p e₀) (weaken p e₁) (weaken-clearing p e₀ x) (weaken-clearing p e₁ x₁)
weaken-clearing p .<> C<> = C<>
weaken-clearing p .(μ e) (Cμ e x) = Cμ (weaken (⊆-cons p) e) (weaken-clearing (⊆-cons p) e x)
weaken-clearing p .⊥ C⊥ = C⊥
weaken-clearing p .(e ⇓ ℓ') (C⇓ e ℓ' x x₁) = C⇓ (weaken p e) ℓ' x (weaken-clearing p e x₁)
weaken-clearing p (⟨_*_∶_⟩ {Γ} {t} ℓ* e₂ e₃) (Cf e₂ e₃ ℓ' x x₁) = Cf (weaken p e₂) (weaken p e₃) ℓ' x (weaken-clearing p e₂ x₁)

var-subst-clearing : ∀{s t ℓ*}
                   → (Γ Γ' : Ctx)
                   → (e : Γ' ⊢ s)
                   → (p : t ∈ (Γ ++ [ s ] ++ Γ'))
                   → ℓ* clears e
                   → ℓ* clears var-subst Γ Γ' e p
var-subst-clearing [] Γ' e hd x = x
var-subst-clearing [] Γ' e (tl p) x = CVar p
var-subst-clearing (x₁ ∷ Γ) Γ' e hd x = CVar hd
var-subst-clearing (x₁ ∷ Γ) Γ' e (tl p) x =
  let cl = var-subst-clearing Γ Γ' e p x in
  weaken-clearing (λ {x₂} → tl) (var-subst Γ Γ' e p) (var-subst-clearing Γ Γ' e p x)

tm-subst-clearing : ∀{s t ℓ*}
                  → (Γ Γ' : Ctx) 
                  → (e : Γ' ⊢ s)
                  → (e' : (Γ ++ [ s ] ++ Γ') ⊢ t)
                  → ℓ* clears e
                  → ℓ* clears e'
                  → ℓ* clears tm-subst Γ Γ' e e'
tm-subst-clearing Γ Γ' e (Var x₂) x x₁ = var-subst-clearing Γ Γ' e x₂ x
tm-subst-clearing Γ Γ' e (λ' e') x (Cλ' .e' x₁) = Cλ' (tm-subst (_ ∷ Γ) Γ' e e') (tm-subst-clearing (_ ∷ Γ) Γ' e e' x x₁)
tm-subst-clearing Γ Γ' e (e' • e'') x (C• .e' .e'' x₁ x₂) = C• (tm-subst Γ Γ' e e') (tm-subst Γ Γ' e e'') (tm-subst-clearing Γ Γ' e e' x x₁) (tm-subst-clearing Γ Γ' e e'' x x₂)
tm-subst-clearing Γ Γ' e <> x x₁ = C<>
tm-subst-clearing Γ Γ' e (μ e') x (Cμ .e' x₁) = Cμ (tm-subst (_ ∷ Γ) Γ' e e') (tm-subst-clearing (_ ∷ Γ) Γ' e e' x x₁)
tm-subst-clearing Γ Γ' e ⊥ x x₁ = C⊥
tm-subst-clearing Γ Γ' e (e' ⇓ x₂) x (C⇓ .e' .x₂ x₁ x₃) = C⇓ (tm-subst Γ Γ' e e') x₂ x₁ (tm-subst-clearing Γ Γ' e e' x x₃)
tm-subst-clearing Γ Γ' e ⟨ x * e' ∶ e'' ⟩ x₁ (Cf .e' .e'' ℓ' x₂ x₃) = Cf (tm-subst Γ Γ' e e') (tm-subst Γ Γ' e e'') ℓ' x₂ (tm-subst-clearing Γ Γ' e e' x₁ x₃)

clearing-↓ : ∀{Γ t ℓ} → (e : Γ ⊢ t) → ℓ clears (e ↓ ℓ)
clearing-↓ {ℓ = ℓ} (Var x) = CVar x
clearing-↓ {ℓ = ℓ} (λ' e) = Cλ' (e ↓ ℓ) (clearing-↓ e)
clearing-↓ {ℓ = ℓ} (e • e₁) = C• (e ↓ ℓ) (e₁ ↓ ℓ) (clearing-↓ e) (clearing-↓ e₁)
clearing-↓ {ℓ = ℓ} <> = C<>
clearing-↓ {ℓ = ℓ} ⟨ x * e ∶ e₁ ⟩ with x ?⊑ ℓ
... | yes p = clearing-↓ e
... | no ¬p = clearing-↓ e₁
clearing-↓ {ℓ = ℓ} (μ e) = Cμ (e ↓ ℓ) (clearing-↓ e)
clearing-↓ {ℓ = ℓ} ⊥ = C⊥
clearing-↓ {ℓ = ℓ} (e ⇓ x) with ℓ ?⊨ x
... | yes p = clearing-↓ e
... | no ¬p = C⊥

clearing-step : ∀{Γ t ℓ} (e e' : Γ ⊢ t) → ℓ clears e → e ⟶s e' → ℓ clears e'
clearing-step .(Var p) e' (CVar p) ()
clearing-step .(λ' e) e' (Cλ' e x) ()
clearing-step .(e₀ • e₁) .(_ • e₁) (C• e₀ e₁ x x₂) (AppCs x₁) = C• _ e₁ (clearing-step e₀ _ x x₁) x₂
clearing-step .(λ' e • e₁) _ (C• .(λ' e) e₁ (Cλ' e x) x₂) AppRs = tm-subst-clearing _ _ _ _ x₂ x
clearing-step .(⊥ • e₁) .⊥ (C• .⊥ e₁ x x₂) ⊥Apps = C⊥
clearing-step .<> e' C<> ()
clearing-step .(μ e) .(tm-subst [] _ (μ e) e) (Cμ e x) Recs = tm-subst-clearing _ _ _ _ (Cμ e x) x
clearing-step .⊥ e' C⊥ ()
clearing-step .(e ⇓ ℓ') .e (C⇓ e ℓ' x x₂) ⇓igns = x₂
clearing-step (⟨_*_∶_⟩ {Γ} {t} ℓ e₂ e₃) .e₂ (Cf e₂ e₃ ℓ' x x₁) FacEs = x₁

facet-step-~⟨ℓ⟩ : ∀{Γ t ℓ} → (e₀ e₁ e₂ : Γ ⊢ t) → e₀ ~⟨ ℓ ⟩ e₁ → e₀ ⟶f e₂ → ∃[ e₃ ](e₁ ⟶f* e₃ × e₂ ~⟨ ℓ ⟩ e₃)
facet-step-~⟨ℓ⟩ {ℓ = ℓ} e₀ e₁ e₂ x x₁ with projection {ℓ = ℓ} e₀ e₂ x₁
facet-step-~⟨ℓ⟩ {ℓ = ℓ} e₀ e₁ e₂ x x₁ | inj₁ x₂ with simulation {ℓ = ℓ} e₁ (e₂ ↓ ℓ) (coerce (cong₂ _⟶s_ x refl) x₂)
... | tm , red , eq = tm , red , trans (↓-idempotent {e = e₂}) (sym eq)
facet-step-~⟨ℓ⟩ {ℓ = ℓ} e₀ e₁ e₂ x x₁ | inj₂ y = e₁ , ref , trans (sym y) x

repeated-facet-step-~⟨ℓ⟩ : ∀{Γ t ℓ} → (e₀ e₁ e₂ : Γ ⊢ t) → e₀ ~⟨ ℓ ⟩ e₁ → e₀ ⟶f* e₂ → ∃[ e₃ ](e₁ ⟶f* e₃ × e₂ ~⟨ ℓ ⟩ e₃)
repeated-facet-step-~⟨ℓ⟩ e₀ e₁ .e₀ x ref = e₁ , ref , x
repeated-facet-step-~⟨ℓ⟩ e₀ e₁ e₂ x (_﹔_ {e' = e'} x₁ x₂) with facet-step-~⟨ℓ⟩ e₀ e₁ e' x x₁
repeated-facet-step-~⟨ℓ⟩ {ℓ = ℓ} e₀ e₁ e₂ x (_﹔_ {e' = e'} x₁ x₂) | tm , red , eq with repeated-facet-step-~⟨ℓ⟩ {ℓ = ℓ} e' tm e₂ eq x₂
... | tm' , red' , eq' = tm' , ⟶f*++ red red' , eq'

repeated-clearing-simulation : ∀{Γ t ℓ} → (e e' : Γ ⊢ t) → ℓ clears e → (sr : e ⟶s* e')
                             → ∃[ e'' ] (e ⟶f* e'' × e' ~⟨ ℓ ⟩ e'')
repeated-clearing-simulation e .e x ref = e , ref , refl
repeated-clearing-simulation {ℓ = ℓ} e e' x (_﹔_ {e' = ex} x₂ sr) =
  let tm  , red  , pr  = clearing-simulation e _ x x₂ in
  let tm' , red' , pr' = repeated-clearing-simulation {ℓ = ℓ} ex e' (clearing-step e _ x x₂) sr in
  let tm'' , red'' , pr'' = repeated-facet-step-~⟨ℓ⟩ ex tm tm' (sym pr) red' in
  tm'' , ⟶f*++ red red'' , trans pr' pr''

compat₀ : ∀{Γ t} → L → Γ ⊢ t → Set
compat₀ ℓ ⟨ ℓ₁ * e₀ ∶ e₁ ⟩ = ℓ ≡ ℓ₁ × e₀ ↓ ℓ ≡ e₀
compat₀ _ _ = ⊥⊥

compatible : ∀{Γ t} → L → Γ ⊢ t → Set
compatible ℓ e = compat₀ ℓ e ⊎ (e ↓ ℓ ≡ e)

secure : ∀{Γ t₀ t₁} → L → L → t₀ ∷ Γ ⊢ t₁ → Set
secure {Γ} {t₀} {t₁} ℓi ℓ e =
  ∀{e₀ e₁ : Γ ⊢ t₀}{v₀ : Γ ⊢ t₁}
  → compatible ℓi e₀ → compatible ℓi e₁
  → e₀ ~⟨ ℓ ⟩ e₁
  → (StdValue v₀ → (e / e₀) ⟶s* v₀ → ∃[ v₁ ] (StdValue v₁ × (e / e₁) ⟶s* v₁ × v₀ ~⟨ ℓ ⟩ v₁))

transparency : ∀{Γ t₀ t₁ ℓ ℓi}
              → (e : t₀ ∷ Γ ⊢ t₁) 
              → secure ℓi ℓ e
              → ℓ clears e
              → (e₀ : Γ ⊢ t₀)
              → compatible ℓi e₀
              → (v : Γ ⊢ t₁)
              → StdValue v
              → (e / e₀) ⟶s* v
              → ∃[ e'' ] ((e / e₀) ⟶f* e'' × v ~⟨ ℓ ⟩ e'')
transparency {ℓ = ℓ} {ℓi} e x x₁ e₀ compat v val x₂ =
  let sec = x {e₀ = e₀} {e₁ = e₀ ↓ ℓ} {v₀ = v} compat (inj₂ (sym (↓-idempotent₂ e₀))) (↓-idempotent {e = e₀}) in
  let tm , val , red , pr = sec val x₂ in
  let tm' , red' , pr' = repeated-clearing-simulation {ℓ = ℓ}
                            (tm-subst [] _ (e₀ ↓ ℓ) e) tm
                            (tm-subst-clearing [] _ (e₀ ↓ ℓ) e (clearing-↓ e₀) x₁) red
                                                              in
  let tm'' , red'' , pr'' = repeated-facet-step-~⟨ℓ⟩ {ℓ = ℓ}
                            (tm-subst [] _ (e₀  ↓ ℓ) e)
                            (tm-subst [] _ e₀ e) tm'
                            (trans (↓-idempotent {e = tm-subst _ _ (e₀ ↓ ℓ) e}) (trans (cong₂ _↓_ (tm-subst-↓ _ _ (e₀ ↓ ℓ) e) refl)
                            (trans (cong (λ e₁ → tm-subst [] _ e₁ (e ↓ ℓ) ↓ ℓ) (sym (↓-idempotent {e = e₀})))
                            (trans (cong₂ _↓_ (sym (tm-subst-↓ {ℓ* = ℓ} [] _ e₀ e)) refl) (sym (↓-idempotent {e = tm-subst _ _ e₀ e}))))))
                            red' in
  tm'' , red'' , trans pr (trans pr' pr'')

single-step-noninterference : ∀{Γ t ℓ}
                            → (e₀ e₁ e₀' : Γ ⊢ t)
                            → e₀ ~⟨ ℓ ⟩ e₁
                            → e₀ ⟶f e₀'
                            → ∃[ e₁' ] (e₁ ⟶f* e₁' × e₀' ~⟨ ℓ ⟩ e₁')
single-step-noninterference {ℓ = ℓ} e₀ e₁ e₀' x x₁ with projection {ℓ = ℓ} e₀ e₀' x₁
single-step-noninterference {ℓ = ℓ} e₀ e₁ e₀' x x₁ | inj₁ x₂ with simulation {ℓ = ℓ} e₁ (e₀' ↓ ℓ) (coerce (cong₂ _⟶s_ x refl) x₂)
single-step-noninterference {ℓ = ℓ} e₀ e₁ e₀' x x₁ | inj₁ x₂ | tm , red , pr = tm , red , sym (trans pr (sym (↓-idempotent {e = e₀'})))
single-step-noninterference {ℓ = ℓ} e₀ e₁ e₀' x x₁ | inj₂ y = _ , ref , trans (sym y) x

noninterference : ∀{Γ t ℓ}
                → (e₀ e₁ e₀' : Γ ⊢ t)
                → e₀ ~⟨ ℓ ⟩ e₁
                → e₀ ⟶f* e₀'
                → ∃[ e₁' ] (e₁ ⟶f* e₁' × e₀' ~⟨ ℓ ⟩ e₁')
noninterference e₀ e₁ .e₀ x ref = e₁ , ref , x
noninterference e₀ e₁ e₀' x (x₁ ﹔ x₂) with single-step-noninterference e₀ e₁ _ x x₁
noninterference e₀ e₁ e₀' x (x₁ ﹔ x₂) | tm , red , pr with noninterference _ tm e₀' pr x₂
... | tm' , red' , pr' = tm' , ⟶f*++ red red' , pr'
