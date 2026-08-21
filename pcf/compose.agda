module pcf.compose where

open import pcf.base
open import pcf.subst
open import pcf.denote

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to bot)
open import Function.Base using (id; _∘_)
open import Relation.Nullary.Negation using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

ℱ : ∀ {Γ A B} → Denotation (Γ ▷ A) B → Denotation Γ (A ⇒ B)
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥       = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)

sub-ℱ : ∀ {Γ A B} {N : Γ ▷ A ⊢ B} {γ : Env Γ} {v u}
  → ℱ (ℰ N) γ v
  → u ⊑ v
    ------------
  → ℱ (ℰ N) γ u
sub-ℱ d ⊑-bot = tt
sub-ℱ d (⊑-conj-L lt lt₁) = sub-ℱ d lt , sub-ℱ d lt₁
sub-ℱ d (⊑-conj-R1 lt) = sub-ℱ (proj₁ d) lt
sub-ℱ d (⊑-conj-R2 lt) = sub-ℱ (proj₂ d) lt
sub-ℱ d (⊑-trans lt lt₁) = sub-ℱ (sub-ℱ d lt₁) lt
sub-ℱ d (⊑-fun lt lt₁) = ↓-sub (up-env d lt) lt₁
sub-ℱ d ⊑-dist = ↓-⊔-intro (proj₁ d) (proj₂ d)

ℰƛ→ℱℰ : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B}{v : Value (A ⇒ B)}
  → ℰ (ƛ N) γ v
    ------------
  → ℱ (ℰ N) γ v
ℰƛ→ℱℰ (↓-↦-intro d) = d
ℰƛ→ℱℰ ↓-⊥-intro = tt
ℰƛ→ℱℰ (↓-⊔-intro d d₁) = ℰƛ→ℱℰ d , ℰƛ→ℱℰ d₁
ℰƛ→ℱℰ (↓-sub d x) = sub-ℱ (ℰƛ→ℱℰ d) x

lambda-inversion : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B} {v₁ v₂}
  → γ ⊢ ƛ N ↓ v₁ ↦ v₂
    -----------------
  → (γ `, v₁) ⊢ N ↓ v₂
lambda-inversion {v₁ = v₁ }{v₂ = v₂} d = ℰƛ→ℱℰ {v = v₁ ↦ v₂} d

ℱℰ→ℰƛ : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B} {v : Value (A ⇒ B)}
  → ℱ (ℰ N) γ v
    ------------
  → ℰ (ƛ N) γ v
ℱℰ→ℰƛ {v = ⊥} d = ↓-⊥-intro
ℱℰ→ℰƛ {v = v₁ ↦ v₂} d = ↓-↦-intro d
ℱℰ→ℰƛ {v = v₁ ⊔ v₂} (d1 , d2) = ↓-⊔-intro (ℱℰ→ℰƛ d1) (ℱℰ→ℰƛ d2)

lam-equiv : ∀ {Γ} {A B} {N : Γ ▷ A ⊢ B} → ℰ (ƛ N) ≃ ℱ (ℰ N)
lam-equiv γ v = ℰƛ→ℱℰ , ℱℰ→ℰƛ

𝒵 : ∀ {Γ} → Denotation Γ `ℕ
𝒵 γ v = v ⊑ lit zero

sub-𝒵 : ∀ {Γ} {γ : Env Γ} {v u}
  → 𝒵 γ v
  → u ⊑ v
    ------
  → 𝒵 γ u
sub-𝒵 d lt =  ⊑-trans lt d

ℰ→𝒵 : ∀ {Γ} {γ : Env Γ} {v} 
  → ℰ `Z γ v
    --------
  → 𝒵 γ v
ℰ→𝒵 ↓-⊥-intro = ⊑-bot
ℰ→𝒵 (↓-⊔-intro d d₁) = ⊑-conj-L (ℰ→𝒵 d) (ℰ→𝒵 d₁)
ℰ→𝒵 (↓-sub d x) = ⊑-trans x (ℰ→𝒵 d)
ℰ→𝒵 ↓-Z = ⊑-lit

𝒵→ℰ : ∀ {Γ} {γ : Env Γ} {v} 
  → 𝒵 γ v
    --------
  → ℰ `Z γ v
𝒵→ℰ ⊑-bot = ↓-⊥-intro
𝒵→ℰ ⊑-lit = ↓-Z
𝒵→ℰ (⊑-conj-L d d₁) = ↓-⊔-intro (𝒵→ℰ d) (𝒵→ℰ d₁)
𝒵→ℰ (⊑-trans d d₁) = ↓-sub (𝒵→ℰ d₁) d

zero-equiv : ∀ {Γ} → ℰ `Z ≃ 𝒵 {Γ}
zero-equiv γ v = ℰ→𝒵 , 𝒵→ℰ

𝒮 : ∀ {Γ} → Denotation Γ `ℕ → Denotation Γ `ℕ
𝒮 D γ ⊥ = ⊤
𝒮 D γ (lit zero) = bot
𝒮 D γ (lit (suc x)) = D γ (lit x)
𝒮 D γ (u ⊔ v) =  (𝒮 D γ u) × (𝒮 D γ v)

sub-𝒮 : ∀ {Γ} {N : Γ ⊢ `ℕ} {γ : Env Γ} {v u}
  → 𝒮 (ℰ N) γ v
  → u ⊑ v
  →  𝒮 (ℰ N) γ u
sub-𝒮 d ⊑-bot = tt
sub-𝒮 d ⊑-lit = d
sub-𝒮 d (⊑-conj-L lt lt₁) = sub-𝒮 d lt , sub-𝒮 d lt₁
sub-𝒮 d (⊑-conj-R1 lt) = sub-𝒮 (d .proj₁) lt
sub-𝒮 d (⊑-conj-R2 lt) = sub-𝒮 (d .proj₂) lt
sub-𝒮 d (⊑-trans lt lt₁) = sub-𝒮 (sub-𝒮 d lt₁) lt

ℰS→𝒮ℰ : ∀ {Γ} {γ : Env Γ} {N : Γ ⊢ `ℕ} {v : Value `ℕ}
  → ℰ (`S N) γ v
    ------------
  → 𝒮 (ℰ N) γ v
ℰS→𝒮ℰ ↓-⊥-intro = tt
ℰS→𝒮ℰ (↓-⊔-intro d d₁) = ℰS→𝒮ℰ d , ℰS→𝒮ℰ d₁
ℰS→𝒮ℰ (↓-sub d x) = sub-𝒮 (ℰS→𝒮ℰ d) x
ℰS→𝒮ℰ (↓-S d) = d

𝒮ℰ→ℰS : ∀ {Γ} {γ : Env Γ} {N : Γ ⊢ `ℕ} {v : Value `ℕ}
  → 𝒮 (ℰ N) γ v
    ------------
  → ℰ (`S N) γ v
𝒮ℰ→ℰS {v = ⊥} d = ↓-⊥-intro
𝒮ℰ→ℰS {v = lit (suc x)} d = ↓-S d
𝒮ℰ→ℰS {v = v ⊔ v₁} d = ↓-⊔-intro (𝒮ℰ→ℰS (d .proj₁)) (𝒮ℰ→ℰS (d .proj₂))

suc-equiv : ∀ {Γ} {N : Γ ⊢ `ℕ} → ℰ (`S N) ≃ 𝒮 (ℰ N)
suc-equiv γ v = ℰS→𝒮ℰ , 𝒮ℰ→ℰS

