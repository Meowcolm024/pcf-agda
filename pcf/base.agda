module pcf.base where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as RT
open RT using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Function.Base using (id; _∘_)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      ------------------------
    → f ≡ g

infixr 7 _⇒_

data Ty : Set where
  `ℕ  : Ty
  _⇒_ : Ty → Ty → Ty

infixl 5 _▷_

data Ctx : Set where
  ∅   : Ctx
  _▷_ : Ctx → Ty → Ctx

infix  4 _∋_

data _∋_ : Ctx → Ty → Set where
  Z : ∀ {Γ A}           → Γ ▷ A ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → Γ ▷ B ∋ A

infix  4 _⊢_

infix  9 `_
infixr 5 ƛ_ μ_
infixl 7 _·_

data _⊢_ (Γ : Ctx) : Ty → Set where
  `_   : ∀ {A}   → Γ ∋ A                       → Γ ⊢ A
  ƛ_   : ∀ {A B} → Γ ▷ A ⊢ B                   → Γ ⊢ A ⇒ B
  _·_  : ∀ {A B} → Γ ⊢ A ⇒ B      → Γ ⊢ A      → Γ ⊢ B
  `Z   :                                         Γ ⊢ `ℕ
  `S   :           Γ ⊢ `ℕ                      → Γ ⊢ `ℕ 
  case : ∀ {A}   → Γ ⊢ `ℕ → Γ ⊢ A → Γ ▷ `ℕ ⊢ A → Γ ⊢ A
  μ_   : ∀ {A}   → Γ ▷ A ⊢ A                   → Γ ⊢ A

size : Ctx → ℕ
size ∅        = zero
size (Γ ▷ A) = suc (size Γ)

lookup : ∀ {Γ n} → (n<|Γ| : n < size Γ) → Ty
lookup {Γ ▷ A} {zero}  (s≤s z≤n)   = A
lookup {Γ ▷ A} {suc n} (s≤s n<|Γ|) = lookup n<|Γ|

count : ∀ {Γ n} → (n<|Γ| : n < size Γ) → Γ ∋ lookup n<|Γ|
count {Γ ▷ A} {zero}  (s≤s z≤n)   = Z
count {Γ ▷ A} {suc n} (s≤s n<|Γ|) = S (count n<|Γ|)

infix 9 #_

#_ : ∀ {Γ}
   → (n : ℕ) {n∈Γ : True (suc n ≤? size Γ)}
    ----------------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = ` count (toWitness n∈Γ)

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

lift : ∀ {Γ Δ A} → Ren Γ Δ → Ren (Γ ▷ A) (Δ ▷ A)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

ren : ∀ {Γ Δ} → Ren Γ Δ → ∀ {A} → Γ ⊢ A → Δ ⊢ A
ren ρ (` x)        = ` ρ x
ren ρ (ƛ M)        = ƛ ren (lift ρ) M
ren ρ (M · N)      = (ren ρ M) · (ren ρ N)
ren ρ `Z           = `Z
ren ρ (`S M)       = `S (ren ρ M)
ren ρ (case L M N) = case (ren ρ L) (ren ρ M) (ren (lift ρ) N)
ren ρ (μ M)        = μ ren (lift ρ) M

weaken : ∀ {Γ A B} → Γ ⊢ A → Γ ▷ B ⊢ A
weaken = ren S

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

lifts : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
lifts σ Z     = ` Z
lifts σ (S x) = weaken (σ x)

sub : ∀ {Γ Δ} → Sub Γ Δ → ∀ {A} → Γ ⊢ A → Δ ⊢ A
sub σ (` x)        = σ x
sub σ (ƛ M)        = ƛ sub (lifts σ) M
sub σ (M · N)      = (sub σ M) · (sub σ N)
sub σ `Z           = `Z
sub σ (`S M)       = `S (sub σ M)
sub σ (case L M N) = case (sub σ L) (sub σ M) (sub (lifts σ) N)
sub σ (μ M)        = μ sub (lifts σ) M

infixr 6 _•_

_•_ : ∀ {Γ Δ A} → (M : Δ ⊢ A) → (σ : Sub Γ Δ) → Sub (Γ ▷ A) Δ
(M • σ) Z     = M
(M • σ) (S x) = σ x

ids : ∀ {Γ} → Sub Γ Γ
ids x = ` x

sub-zero : ∀ {Γ A} → Γ ⊢ A → Sub (Γ ▷ A) Γ
sub-zero M = M • ids

_[_] : ∀ {Γ A B} → Γ ▷ B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] M N = sub (sub-zero N) M

data Val {Γ} : ∀ {A} → (Γ ⊢ A) → Set where
  V-Z : Val `Z
  V-S : ∀ {M : Γ ⊢ `ℕ} → Val M → Val (`S M)
  V-ƛ : ∀ {A B} → (M : Γ ▷ A ⊢ B) → Val (ƛ M)

infix  3 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·ₗ : ∀ {Γ A B} {M M' : Γ ⊢ A ⇒ B} {N}
    → M —→ M'
      ----------------
    → M · N —→ M' · N

  ξ-·ᵣ : ∀ {Γ A B} {M : Γ ▷ A ⊢ B} {N N'}
    → N —→ N'
      ------------------------
    → (ƛ M) · N —→ (ƛ M) · N'

  β-· : ∀ {Γ A B} {M : Γ ▷ A ⊢ B} {N}
    → Val N
      ---------------------
    → (ƛ M) · N —→ M [ N ]

  ξ-S : ∀ {Γ} {M M' : Γ ⊢ `ℕ}
    → M —→ M'
      --------------
    → `S M —→ `S M'

  ξ-case : ∀ {Γ A} {L L' : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
    → L —→ L'
      --------------------------
    → case L M N —→ case L' M N

  β-case-Z : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
      ------------------
    → case `Z M N —→ M

  β-case-S : ∀ {Γ A} {L : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
    → Val L
      ---------------------------
    → case (`S L) M N —→ N [ L ]

  β-μ : ∀ {Γ A} {M : Γ ▷ A ⊢ A}
      -------------------
    → (μ M) —→ M [ μ M ]

progress : ∀ {A} → (M : ∅ ⊢ A) → ∃[ N ] (M —→ N) ⊎ Val M
progress (ƛ M)               = inj₂ (V-ƛ M)
progress (M · N) with progress M
... | inj₁ (M' , M—→M')      = inj₁ (M' · N , ξ-·ₗ M—→M')
... | inj₂ (V-ƛ M') with progress N
... | inj₁ (N' , N—→N')      = inj₁ ((ƛ M') · N' , ξ-·ᵣ N—→N')
... | inj₂ VN                = inj₁ ((M' [ N ]) , β-· VN)
progress `Z                  = inj₂ V-Z
progress (`S M) with progress M
... | inj₁ (M' , M—→M')      = inj₁ (`S M' , ξ-S M—→M')
... | inj₂ VM                = inj₂ (V-S VM)
progress (case L M N) with progress L
... | inj₁ (L' , L—→L')      = inj₁ (case L' M N , ξ-case L—→L')
... | inj₂ V-Z               = inj₁ (M , β-case-Z)
... | inj₂ (V-S {M = L'} VL) = inj₁ ((N [ L' ]) , β-case-S VL)
progress (μ M)               = inj₁ ((M [ μ M ]) , β-μ)

infix  2 _—↠_

_—↠_ : ∀ {Γ A} → (M N : Γ ⊢ A) → Set
_—↠_ M N = Star _—→_ M N
