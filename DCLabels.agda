open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Negation
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
module DCLabels where

_⇔_ : Set → Set → Set
a ⇔ b = (a → b) × (b → a)

power : Set → Set
power A = List A

data _∈_ : ∀{A : Set} → A → List A → Set where
  hd : ∀{A}{a : A}{xs : List A} → a ∈ (a ∷ xs)
  tl : ∀{A}{a₀ a₁ : A}{xs : List A} → a₀ ∈ xs → a₀ ∈ (a₁ ∷ xs)

∈[] : ∀{A}{x : A} → ¬ (x ∈ [])
∈[] ()

_∈D_ : (x : ℕ) → (xs : List ℕ) → Dec (x ∈ xs)
x ∈D [] = no (λ ())
x ∈D (x₁ ∷ xs) with x ≟ x₁
... | yes refl = yes hd
x ∈D (x₁ ∷ xs) | no ¬p with x ∈D xs
... | yes q = yes (tl q)
... | no ¬q = no (λ {hd → ¬p refl ; (tl p) → ¬q p})

_⊆_ : ∀{A : Set} → List A → List A → Set
xs ⊆ ys = ∀{x} → x ∈ xs → x ∈ ys

_⊆D_ : (xs ys : List ℕ) → Dec (xs ⊆ ys)
[] ⊆D ys = yes (λ {x} ())
(x ∷ xs) ⊆D ys with x ∈D ys
... | no ¬p = no λ f → ¬p (f hd)
(x ∷ xs) ⊆D ys | yes p with xs ⊆D ys
... | yes p₁ = yes λ { hd → p ; (tl p) → p₁ p }
... | no ¬p₁ = no (λ z → ¬p₁ (λ {x₁} z₁ → z (tl z₁)))

_≅_ : ∀{A : Set} → List A → List A → Set
xs ≅ ys = xs ⊆ ys × ys ⊆ xs

Clause : Set → Set
Clause A = List A

CNF : Set → Set
CNF A = List (Clause A)

_⊃_ : ∀{A} → CNF A → Clause A → Set
ℓ ⊃ c = ∃[ c' ] (c' ∈ ℓ × c' ⊆ c)

¬⊃∷ : ∀{A}{ℓ : CNF A}{c₀ c₁ : Clause A} → ¬ (c₁ ⊆ c₀) → ¬ (ℓ ⊃ c₀) → ¬ ((c₁ ∷ ℓ) ⊃ c₀)
¬⊃∷ x x₁ (fst , hd , snd) = x snd
¬⊃∷ x x₁ (fst , tl fst₁ , snd) = x₁ (fst , fst₁ , snd)

_⊃D_ : (ℓ : CNF ℕ) → (c : Clause ℕ) → Dec (ℓ ⊃ c)
[] ⊃D c = no λ p → ∈[] (proj₁ (proj₂ p))
(x ∷ ℓ) ⊃D c with x ⊆D c
... | yes p = yes (x , hd , p)
(x ∷ ℓ) ⊃D c | no ¬p with ℓ ⊃D c
((x ∷ ℓ) ⊃D c) | no ¬p | yes (fst , fst₁ , snd) = yes (fst , tl fst₁ , snd)
... | no ¬q = no (¬⊃∷ ¬p ¬q)

_⊑cnf_ : ∀{A} → CNF A → CNF A → Set
ℓ ⊑cnf ℓ' = ∀ {c} → c ∈ ℓ → ℓ' ⊃ c

_⊔cnf_ : ∀{A} → CNF A → CNF A → CNF A
ℓ ⊔cnf ℓ' = ℓ ++ ℓ'

_∶_ : CNF ℕ → CNF ℕ → CNF ℕ
ℓ ∶ ℓ' = filter (λ c → ¬? (ℓ' ⊃D c)) ℓ

filter∈ : ∀{A}{x : A}{xs : List A}{P : A → Set}{f : (a : A) → Dec (P a)} → x ∈ xs → P x → x ∈ filter f xs
filter∈ {xs = []} () x₂
filter∈ {xs = x ∷ xs} {f = f} hd x₂ with f x
... | yes p = hd
... | no ¬p = contradiction x₂ ¬p 
filter∈ {xs = x ∷ xs}{f = f} (tl x₁) x₂ with f x
... | yes p = tl (filter∈ {f = f} x₁ x₂)
... | no ¬p = filter∈ {f = f} x₁ x₂

∈++₀ : ∀{A}{x : A}{xs ys : List A} → x ∈ xs → x ∈ (xs ++ ys)
∈++₀ hd = hd
∈++₀ (tl x₁) = tl (∈++₀ x₁)

∈++₁ : ∀{A}{x : A}{xs ys : List A} → x ∈ xs → x ∈ (ys ++ xs)
∈++₁ {ys = []} = λ z → z
∈++₁ {ys = x ∷ ys} = λ z → tl (∈++₁ z)

∈filter : ∀{A}{x : A}{xs : List A}{P : A → Set}{f : (a : A) → Dec (P a)} → x ∈ filter f xs → x ∈ xs
∈filter {xs = []} {f = f} ()
∈filter {xs = x ∷ xs} {f = f} x₁ with f x
∈filter {x = _} {x ∷ xs} {f = f} hd | yes p = hd
∈filter {x = _} {x ∷ xs} {f = f} (tl x₁) | yes p = tl (∈filter {f = f} x₁)
... | no ¬p = tl (∈filter {f = f} x₁)

∈filterpos : ∀{A}{x : A}{xs : List A}{P : A → Set}{f : (a : A) → Dec (P a)} → P x → x ∈ xs → x ∈ filter f xs
∈filterpos {xs = []} x₁ = λ z → z
∈filterpos {xs = x ∷ xs}{f = f} x₁ x₃ with f x
∈filterpos {x = _} {x ∷ xs} {f = f} x₁ hd | yes p = hd
∈filterpos {x = _} {x ∷ xs} {f = f} x₁ (tl x₃) | yes p = tl (∈filterpos {xs = xs} x₁ x₃)
∈filterpos {x = _} {x ∷ xs} {f = f} x₁ hd | no ¬p = contradiction x₁ ¬p
∈filterpos {x = _} {x ∷ xs} {f = f} x₁ (tl x₃) | no ¬p = ∈filterpos {xs = xs} x₁ x₃

⊃⊔ : ∀{c : Clause ℕ}{ℓ₀ ℓ₁ : CNF ℕ} → (ℓ₀ ⊔cnf ℓ₁) ⊃ c → (ℓ₀ ⊃ c) ⊎ (ℓ₁ ⊃ c)
⊃⊔ {ℓ₀ = []} (fst , fst₁ , snd) = inj₂ (fst , fst₁ , snd)
⊃⊔ {ℓ₀ = x ∷ ℓ₀} (.x , hd , snd) = inj₁ (x , hd , snd)
⊃⊔ {ℓ₀ = x ∷ ℓ₀} (fst , tl fst₁ , snd) with ⊃⊔ (fst , fst₁ , snd)
⊃⊔ {_} {x ∷ ℓ₀} (fst , tl fst₁ , snd) | inj₁ (fst₂ , fst₃ , snd₁) = inj₁ (fst₂ , tl fst₃ , snd₁)
⊃⊔ {_} {x ∷ ℓ₀} (fst , tl fst₁ , snd) | inj₂ (fst₂ , fst₃ , snd₁) = inj₂ (fst₂ , fst₃ , snd₁)

¬∈filter : ∀{A}{x : A}{xs : List A}{P : A → Set}{f : (a : A) → Dec (P a)} → x ∈ filter (λ c → ¬? (f c)) xs → ¬ (P x)
¬∈filter {xs = []} {f = f} () x₂
¬∈filter {xs = x ∷ xs} {f = f} x₁ x₂ with f x
¬∈filter {x = x₃} {x ∷ xs} {f = f} x₁ x₂ | yes p = ¬∈filter {xs = xs} {f = f} x₁ x₂
¬∈filter {x = _} {x ∷ xs} {f = f} hd x₂ | no ¬p = ¬p x₂
¬∈filter {x = _} {x ∷ xs} {f = f} (tl x₁) x₂ | no ¬p = ¬∈filter {xs = xs} {f = f} x₁ x₂

galois₀ : ∀{ℓ₀ ℓ₁ ℓ₂ : CNF ℕ} → ((ℓ₀ ∶ ℓ₁) ⊑cnf ℓ₂) ⇔ (ℓ₀ ⊑cnf (ℓ₁ ⊔cnf ℓ₂))
proj₁ (galois₀ {ℓ₀} {ℓ₁} {ℓ₂}) x {c} x₁ with ℓ₁ ⊃D c
proj₁ (galois₀ {ℓ₀} {ℓ₁} {ℓ₂}) x {c} x₁ | yes (fst , fst₁ , snd) = fst , ∈++₀ fst₁ , snd
... | no ¬p = let cl , inp , subp = x {c = c} (filter∈ x₁ ¬p) in cl , ∈++₁ inp , subp
proj₂ (galois₀ {ℓ₀} {ℓ₁} {ℓ₂}) x {c} x₁ with x (∈filter {f = λ c₁ → ¬? (ℓ₁ ⊃D c₁)} x₁)
proj₂ (galois₀ {ℓ₀} {ℓ₁} {ℓ₂}) x {c} x₁ | fst , snd , trd with ⊃⊔ {ℓ₀ = ℓ₁} {ℓ₁ = ℓ₂} (fst , snd , trd)
... | inj₁ p = contradiction p ¬⊃
  where
    ¬⊃ : ¬ (ℓ₁ ⊃ c)
    ¬⊃ = ¬∈filter {xs = ℓ₀} {f = λ c₁ → ℓ₁ ⊃D c₁} x₁
... | inj₂ p = p

_⊓cnf_ : ∀{A} → CNF A → CNF A → CNF A
[] ⊓cnf ℓ' = []
(x ∷ ℓ) ⊓cnf ℓ' = map (λ x' → x ++ x') ℓ' ++ (ℓ ⊓cnf ℓ')

_-_ : Clause ℕ → Clause ℕ → Clause ℕ
c - c' = filter (λ x → ¬? (x ∈D c')) c

_/_ : CNF ℕ → CNF ℕ → CNF ℕ
ℓ / ℓ' = foldr _⊓cnf_ [ [] ] (map (λ c' → map (λ c'' → c'' - c') ℓ) ℓ')

∈map : ∀{A B : Set} → (xs : List A) → (x : A) → (f : A → B) → x ∈ xs → (f x) ∈ (map f xs)
∈map .(x ∷ _) x f hd = hd
∈map .(_ ∷ _) x f (tl x₁) = tl (∈map _ x f x₁)

∈mapinv : ∀{A B : Set} → (xs : List A) → (fx : B) → (f : A → B) → fx ∈ (map f xs) → ∃[ x ](x ∈ xs × f x ≡ fx)
∈mapinv [] fx f ()
∈mapinv (x₁ ∷ xs) .(f x₁) f hd = x₁ , hd , refl
∈mapinv (x₁ ∷ xs) fx f (tl x) with ∈mapinv xs fx f x
... | x' , inp , eql = x' , tl inp , eql

∈⊓++ : ∀{c₀ c₁ : Clause ℕ}{ℓ₀ ℓ₁ : CNF ℕ} → c₀ ∈ ℓ₀ → c₁ ∈ ℓ₁ → (c₀ ++ c₁) ∈ (ℓ₀ ⊓cnf ℓ₁)
∈⊓++ {c₀} {c₁} {ℓ₀} {ℓ₁}  hd x₁ = ∈++₀ {x = c₀ ++ c₁} {xs = map (_++_ c₀) ℓ₁} (∈map ℓ₁ c₁ (_++_ c₀) x₁)
∈⊓++ {c₀} {c₁} {a ∷ ℓ₀} {ℓ₁} (tl x) x₁ = ∈++₁ {x = c₀ ++ c₁} {ys = map (_++_ a) ℓ₁} (∈⊓++ x x₁)

∈++⊎ : ∀{A}{x : A}{xs ys : List A} → x ∈ (xs ++ ys) → x ∈ xs ⊎ x ∈ ys
∈++⊎ {xs = []} x₁ = inj₂ x₁
∈++⊎ {xs = x ∷ xs} hd = inj₁ hd
∈++⊎ {xs = x ∷ xs} (tl x₁) with ∈++⊎ {xs = xs} x₁ 
... | inj₁ p = inj₁ (tl p)
... | inj₂ p = inj₂ p

lemma₀ : (ℓ : CNF ℕ) → ℓ ⊓cnf [] ≡ []
lemma₀ [] = refl
lemma₀ (ℓ ∷ ℓ₁) = lemma₀ ℓ₁

∈++⊓ : ∀{c : Clause ℕ}{ℓ₀ ℓ₁ : CNF ℕ} → c ∈ (ℓ₀ ⊓cnf ℓ₁) → ∃[ c₀ ] (∃[ c₁ ] (c₀ ++ c₁ ≡ c × c₀ ∈ ℓ₀ × c₁ ∈ ℓ₁))
∈++⊓ {ℓ₀ = []} {ℓ₁} ()
∈++⊓ {ℓ₀ = x₁ ∷ ℓ₀} {[]} x = contradiction x (absurd (lemma₀ ℓ₀))
  where
    absurd : ∀{x : Clause ℕ}{xs : CNF ℕ} → xs ≡ [] → ¬ x ∈ xs
    absurd refl ()
∈++⊓ {ℓ₀ = x₁ ∷ ℓ₀} {x₂ ∷ ℓ₁} hd = x₁ , x₂ , refl , hd , hd
∈++⊓ {ℓ₀ = x₁ ∷ ℓ₀} {x₂ ∷ ℓ₁} (tl x) with ∈++⊎ {xs = map (_++_ x₁) ℓ₁} x
∈++⊓ {c} {ℓ₀ = x₁ ∷ ℓ₀} {x₂ ∷ ℓ₁} (tl x) | inj₁ p with ∈mapinv ℓ₁ c (_++_ x₁) p
... | c' , inp , eql = x₁ , c' , eql , hd , tl inp
∈++⊓ {ℓ₀ = x₁ ∷ ℓ₀} {x₂ ∷ ℓ₁} (tl x) | inj₂ p with ∈++⊓ {ℓ₀ = ℓ₀} {x₂ ∷ ℓ₁} p
... | c₀ , c₁ , prf , p₀ , p₁ = c₀ , c₁ , prf , tl p₀ , p₁

lemma/ : ∀{ℓ ℓ' c₀ c₁} → c₀ ∈ (ℓ' / ℓ) → c₁ ∈ ℓ → ∃[ c' ] (c' ∈ ℓ' × (c' - c₁) ⊆ c₀)
lemma/ {[]} x ()
lemma/ {x ∷ ℓ} {ℓ'} x₁ x₂ with ∈++⊓ {ℓ₀ = map _ ℓ'} x₁
lemma/ {x ∷ ℓ} {ℓ'} {c₁ = .x} x₁ hd | c₀ , c₁ , refl , fst , snd with ∈mapinv ℓ' _ _ fst
lemma/ {x ∷ ℓ} {ℓ'} {_} {.x} x₁ hd | c₀ , c₁ , refl , fst , snd | fst₁ , fst₂ , refl = fst₁ , fst₂ , λ ptr → ∈++₀ {xs = c₀} ptr
lemma/ {x ∷ ℓ} {ℓ'} {c₁ = c₁₀} x₁ (tl x₂) | c₀ , c₁ , refl , fst , snd with lemma/ snd x₂
lemma/ {x ∷ ℓ} {ℓ'} {c₁ = c₁₀} x₁ (tl x₂) | c₀ , c₁ , refl , fst , snd | fst₁ , fst₂ , snd₁ = fst₁ , fst₂ , λ ptr → ∈++₁ {xs = c₁} (snd₁ ptr)

dec-⊎ : ∀{P : Set} → Dec P → P ⊎ ¬ P
dec-⊎ (yes p) = inj₁ p
dec-⊎ (no ¬p) = inj₂ ¬p

galois₁ : ∀{ℓ₀ ℓ₁ ℓ₂ : CNF ℕ} → ((ℓ₀ ⊓cnf ℓ₁) ⊑cnf ℓ₂) ⇔ (ℓ₀ ⊑cnf (ℓ₂ / ℓ₁))
proj₁ (galois₁ {ℓ₀} {ℓ₁} {ℓ₂}) x {c} x₁ = x''' x₁
  where
    x' : ∀{c₀ c₁} → c₀ ∈ ℓ₀ → c₁ ∈ ℓ₁ → ∃[ c' ] (c' ∈ ℓ₂ × c' ⊆ (c₀ ++ c₁))
    x' x₂ x₃ = x (∈⊓++ x₂ x₃)
    
    x'' : ∀{c₀ c₁} → c₀ ∈ ℓ₀ → c₁ ∈ ℓ₁ → ∃[ c' ] (c' ∈ ℓ₂ × (c' - c₁) ⊆ c₀)
    x'' {c₀} {c₁} x₂ x₃ with x' x₂ x₃
    ... | c' , inp , subp = c' , inp , λ {x} x₄ → [ (λ x₅ → x₅) ,
      (λ p → contradiction p (¬∈filter {xs = c'} {P = λ x₅ → x₅ ∈ c₁} {f = λ x₅ → x₅ ∈D c₁} x₄)) ]′ (∈++⊎ (subp (∈filter x₄)))

    helper : ∀{c₀} → (ℓ ℓ' : CNF ℕ) → (∀{c'} → c' ∈ ℓ → ∃[ c'' ] (c'' ∈ ℓ' × (c'' - c') ⊆ c₀)) → ∃[ c' ] (c' ∈ (ℓ' / ℓ) × c' ⊆ c₀)
    helper [] ℓ' x₂ = [] , hd , λ {x₃} ()
    helper (x ∷ ℓ) ℓ' x₂ with x₂ hd
    helper (x ∷ ℓ) ℓ' x₂ | fst , fst₁ , snd with helper ℓ ℓ' (λ c₁ → x₂ (tl c₁))
    helper (x ∷ ℓ) ℓ' x₂ | fst , fst₁ , snd | fst₂ , fst₃ , snd₁ =
      filter (λ x₄ → ¬? (x₄ ∈D x)) fst ++ fst₂
      , ∈⊓++ (∈map ℓ' fst (filter (λ x₃ → ¬? (x₃ ∈D x))) fst₁) fst₃
      , λ pr → [ snd , snd₁ ]′ (∈++⊎ {ys = fst₂} pr)

    x''' : ∀{c₀} → c₀ ∈ ℓ₀ → ∃[ c' ] (c' ∈ (ℓ₂ / ℓ₁) × c' ⊆ c₀)
    x''' {c₀} x₂ = helper ℓ₁ ℓ₂ (x'' x₂)
proj₂ (galois₁ {ℓ₀} {ℓ₁} {ℓ₂}) x {c} x₁ = x'''
  where
    helper : ∀{c₀ c₁} → (ℓ ℓ' : CNF ℕ) → (∃[ c' ] (c' ∈ (ℓ' / ℓ) × c' ⊆ c₀)) → c₁ ∈ ℓ → ∃[ c' ] (c' ∈ ℓ' × (c' - c₁) ⊆ c₀)
    helper ℓ ℓ' (fst , fst₁ , snd) x with lemma/ {ℓ} {ℓ'} fst₁ x
    ... | c'' , inp , subp = c'' , inp , λ {x₂} z → snd (subp z)
        
    x' : ∀{c₀ c₁} → c₀ ∈ ℓ₀ → c₁ ∈ ℓ₁ → ∃[ c' ] (c' ∈ ℓ₂ × (c' - c₁) ⊆ c₀)
    x' {c₀} {c₁} x₂ x₃ = helper {c₀ = c₀} {c₁ = c₁} ℓ₁ ℓ₂ (x x₂) x₃

    x'' : ∀{c₀ c₁} → c₀ ∈ ℓ₀ → c₁ ∈ ℓ₁ → ∃[ c' ] (c' ∈ ℓ₂ × c' ⊆ (c₀ ++ c₁))
    x'' {c₀} {c₁} x₂ x₃ with x' x₂ x₃
    ... | c' , inp , subp = c' , inp , λ {x} p → [ (λ ptr → ∈++₁ {xs = c₁} ptr)
                                                 , (λ ¬ptr → ∈++₀ {xs = c₀} (subp (∈filterpos {xs = c'} ¬ptr p))) ]′
                                                 (dec-⊎ (x ∈D c₁))

    x''' : ∃[ c' ] (c' ∈ ℓ₂ × c' ⊆ c)
    x''' with ∈++⊓ {ℓ₀ = ℓ₀} x₁
    ... | c₀ , c₁ , refl , inp₀ , inp₁ = x'' inp₀ inp₁

DC : Set → Set
DC A = CNF A × CNF A

_⊑_ : ∀{A} → DC A → DC A → Set
(ℓc₀ , ℓi₀) ⊑ (ℓc₁ , ℓi₁) = (ℓc₀ ⊑cnf ℓc₁) × (ℓi₁ ⊑cnf ℓi₀)

_⊔_ : ∀{A} → DC A → DC A → DC A
(ℓc₀ , ℓi₀) ⊔ (ℓc₁ , ℓi₁) = (ℓc₀ ⊔cnf ℓc₁) , (ℓi₀ ⊓cnf ℓi₁)
