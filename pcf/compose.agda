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
sub-ℱ d ⊑-bot             = tt
sub-ℱ d (⊑-conj-L lt lt₁) = sub-ℱ d lt , sub-ℱ d lt₁
sub-ℱ d (⊑-conj-R1 lt)    = sub-ℱ (proj₁ d) lt
sub-ℱ d (⊑-conj-R2 lt)    = sub-ℱ (proj₂ d) lt
sub-ℱ d (⊑-trans lt lt₁)  = sub-ℱ (sub-ℱ d lt₁) lt
sub-ℱ d (⊑-fun lt lt₁)    = ↓-sub (up-env d lt) lt₁
sub-ℱ d ⊑-dist            = ↓-⊔-intro (proj₁ d) (proj₂ d)

ℰƛ→ℱℰ : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B}{v : Value (A ⇒ B)}
  → ℰ (ƛ N) γ v
    ------------
  → ℱ (ℰ N) γ v
ℰƛ→ℱℰ (↓-↦-intro d)    = d
ℰƛ→ℱℰ ↓-⊥-intro        = tt
ℰƛ→ℱℰ (↓-⊔-intro d d₁) = ℰƛ→ℱℰ d , ℰƛ→ℱℰ d₁
ℰƛ→ℱℰ (↓-sub d x)      = sub-ℱ (ℰƛ→ℱℰ d) x

lambda-inversion : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B} {v₁ v₂}
  → γ ⊢ ƛ N ↓ v₁ ↦ v₂
    -----------------
  → (γ `, v₁) ⊢ N ↓ v₂
lambda-inversion {v₁ = v₁ }{v₂ = v₂} d = ℰƛ→ℱℰ {v = v₁ ↦ v₂} d

ℱℰ→ℰƛ : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B} {v : Value (A ⇒ B)}
  → ℱ (ℰ N) γ v
    ------------
  → ℰ (ƛ N) γ v
ℱℰ→ℰƛ {v = ⊥}       d         = ↓-⊥-intro
ℱℰ→ℰƛ {v = v₁ ↦ v₂} d         = ↓-↦-intro d
ℱℰ→ℰƛ {v = v₁ ⊔ v₂} (d₁ , d₂) = ↓-⊔-intro (ℱℰ→ℰƛ d₁) (ℱℰ→ℰƛ d₂)

lam-equiv : ∀ {Γ} {A B} {N : Γ ▷ A ⊢ B} → ℰ (ƛ N) ≃ ℱ (ℰ N)
lam-equiv γ v = ℰƛ→ℱℰ , ℱℰ→ℰƛ

infixl 7 _●_

_●_ : ∀ {Γ A B} → Denotation Γ (A ⇒ B) → Denotation Γ A → Denotation Γ B
(D₁ ● D₂) γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value _ ]( D₁ γ (v ↦ w) × D₂ γ v )

ℰ·→●ℰ : ∀{Γ} {γ : Env Γ} {A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {v}
  → ℰ (L · M) γ v
    ----------------
  → (ℰ L ● ℰ M) γ v
ℰ·→●ℰ (↓-↦-elim {v = v'} d d₁) = inj₂ (v' , d , d₁)
ℰ·→●ℰ ↓-⊥-intro = inj₁ ⊑-bot
ℰ·→●ℰ (↓-⊔-intro {v = v₁} {w = v₂} d₁ d₂)
    with ℰ·→●ℰ d₁ | ℰ·→●ℰ d₂
... | inj₁ lt1 | inj₁ lt2 = inj₁ (⊑-conj-L lt1 lt2)
... | inj₁ lt1 | inj₂ (v₁' , d₁' , d₂') = inj₂ (v₁' , ↓-sub d₁' lt , d₂')
    where lt = ⊑-fun ⊑-refl (⊑-conj-L (⊑-trans lt1 ⊑-bot) ⊑-refl)
... | inj₂ (v₁' , d₁' , d₂') | inj₁ lt2 = inj₂ (v₁' , ↓-sub d₁' lt , d₂')
    where lt = (⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans lt2 ⊑-bot)))
... | inj₂ (v₁' , d₁' , d₂') | inj₂ (v₁'' , d₁'' , d₂'') =
    inj₂ (v₁' ⊔ v₁'' , ↓-sub (↓-⊔-intro d₁' d₁'') ⊔↦⊔-dist , ↓-⊔-intro d₂' d₂'')
ℰ·→●ℰ (↓-sub d x)
    with ℰ·→●ℰ d
... | inj₁ lt = inj₁ (⊑-trans x lt)
... | inj₂ (v₁' , d₁' , d₂') = inj₂ (v₁' , ↓-sub d₁' (⊑-fun ⊑-refl x) , d₂')

●ℰ→ℰ· : ∀{Γ} {γ : Env Γ} {A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} {v}
  → (ℰ L ● ℰ M) γ v
    ----------------
  → ℰ (L · M) γ v
●ℰ→ℰ· (inj₁ x) = ↓-sub ↓-⊥-intro x
●ℰ→ℰ· (inj₂ y) = ↓-↦-elim (y .proj₂ .proj₁) (y .proj₂ .proj₂)

app-equiv : ∀ {Γ} {A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} → ℰ (L · M) ≃ (ℰ L) ● (ℰ M)
app-equiv γ v = ℰ·→●ℰ , ●ℰ→ℰ·

var-inv : ∀ {Γ A} {γ : Env Γ} {x : Γ ∋ A} {v}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ γ x
var-inv ↓-var            = ⊑-refl
var-inv ↓-⊥-intro        = ⊑-bot
var-inv (↓-⊔-intro d d₁) = ⊑-conj-L (var-inv d) (var-inv d₁)
var-inv (↓-sub d x)      = ⊑-trans x (var-inv d)

var-equiv : ∀{Γ A} {x : Γ ∋ A} → ℰ (` x) ≃ (λ γ v → v ⊑ γ x)
var-equiv γ v = var-inv , (λ lt → ↓-sub ↓-var lt)

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
ℰ→𝒵 ↓-⊥-intro        = ⊑-bot
ℰ→𝒵 (↓-⊔-intro d d₁) = ⊑-conj-L (ℰ→𝒵 d) (ℰ→𝒵 d₁)
ℰ→𝒵 (↓-sub d x)      = ⊑-trans x (ℰ→𝒵 d)
ℰ→𝒵 ↓-Z              = ⊑-lit

𝒵→ℰ : ∀ {Γ} {γ : Env Γ} {v} 
  → 𝒵 γ v
    --------
  → ℰ `Z γ v
𝒵→ℰ ⊑-bot           = ↓-⊥-intro
𝒵→ℰ ⊑-lit           = ↓-Z
𝒵→ℰ (⊑-conj-L d d₁) = ↓-⊔-intro (𝒵→ℰ d) (𝒵→ℰ d₁)
𝒵→ℰ (⊑-trans d d₁)  = ↓-sub (𝒵→ℰ d₁) d

zero-equiv : ∀ {Γ} → ℰ `Z ≃ 𝒵 {Γ}
zero-equiv γ v = ℰ→𝒵 , 𝒵→ℰ

𝒮 : ∀ {Γ} → Denotation Γ `ℕ → Denotation Γ `ℕ
𝒮 D γ ⊥             = ⊤
𝒮 D γ (lit zero)    = bot
𝒮 D γ (lit (suc x)) = D γ (lit x)
𝒮 D γ (u ⊔ v)       =  (𝒮 D γ u) × (𝒮 D γ v)

sub-𝒮 : ∀ {Γ} {N : Γ ⊢ `ℕ} {γ : Env Γ} {v u}
  → 𝒮 (ℰ N) γ v
  → u ⊑ v
    -------------
  →  𝒮 (ℰ N) γ u
sub-𝒮 d ⊑-bot             = tt
sub-𝒮 d ⊑-lit             = d
sub-𝒮 d (⊑-conj-L lt lt₁) = sub-𝒮 d lt , sub-𝒮 d lt₁
sub-𝒮 d (⊑-conj-R1 lt)    = sub-𝒮 (d .proj₁) lt
sub-𝒮 d (⊑-conj-R2 lt)    = sub-𝒮 (d .proj₂) lt
sub-𝒮 d (⊑-trans lt lt₁)  = sub-𝒮 (sub-𝒮 d lt₁) lt

ℰS→𝒮ℰ : ∀ {Γ} {γ : Env Γ} {N : Γ ⊢ `ℕ} {v : Value `ℕ}
  → ℰ (`S N) γ v
    -------------
  → 𝒮 (ℰ N) γ v
ℰS→𝒮ℰ ↓-⊥-intro        = tt
ℰS→𝒮ℰ (↓-⊔-intro d d₁) = ℰS→𝒮ℰ d , ℰS→𝒮ℰ d₁
ℰS→𝒮ℰ (↓-sub d x)      = sub-𝒮 (ℰS→𝒮ℰ d) x
ℰS→𝒮ℰ (↓-S d)          = d

𝒮ℰ→ℰS : ∀ {Γ} {γ : Env Γ} {N : Γ ⊢ `ℕ} {v : Value `ℕ}
  → 𝒮 (ℰ N) γ v
    -------------
  → ℰ (`S N) γ v
𝒮ℰ→ℰS {v = ⊥}           d = ↓-⊥-intro
𝒮ℰ→ℰS {v = lit (suc x)} d = ↓-S d
𝒮ℰ→ℰS {v = v ⊔ v₁}      d = ↓-⊔-intro (𝒮ℰ→ℰS (d .proj₁)) (𝒮ℰ→ℰS (d .proj₂))

suc-equiv : ∀ {Γ} {N : Γ ⊢ `ℕ} → ℰ (`S N) ≃ 𝒮 (ℰ N)
suc-equiv γ v = ℰS→𝒮ℰ , 𝒮ℰ→ℰS

data CaseS {Γ A} (D₂ : Denotation Γ A) (D₃ : Denotation (Γ ▷ `ℕ) A) (γ : Env Γ)
  : Value `ℕ → Value A → Set where

  cs-Z   : ∀ {w} → D₂ γ w → CaseS D₂ D₃ γ (lit zero) w

  cs-S   : ∀ {n w} → D₃ (γ `, lit n) w → CaseS D₂ D₃ γ (lit (suc n)) w

  cs-⊔   : ∀ {u u' w w'} → CaseS D₂ D₃ γ u w → CaseS D₂ D₃ γ u' w'
         → CaseS D₂ D₃ γ (u ⊔ u') (w ⊔ w')

  cs-sub : ∀ {u w v} → CaseS D₂ D₃ γ u w → v ⊑ w → CaseS D₂ D₃ γ u v
         
𝒞 : ∀ {Γ A} → Denotation Γ `ℕ → Denotation Γ A → Denotation (Γ ▷ `ℕ) A → Denotation Γ A
𝒞 D₁ D₂ D₃ γ w = w ⊑ ⊥ ⊎ (∃[ u ] (D₁ γ u × CaseS D₂ D₃ γ u w))

ℰcase→𝒞ℰ : ∀ {Γ} {γ : Env Γ} {A} {L M} {N : Γ ▷ `ℕ ⊢ A} {v : Value A}
  → ℰ (case L M N) γ v
    ------------------------
  → 𝒞 (ℰ L) (ℰ M) (ℰ N) γ v
ℰcase→𝒞ℰ ↓-⊥-intro = inj₁ ⊑-bot
ℰcase→𝒞ℰ (↓-⊔-intro d₁ d₂)
    with ℰcase→𝒞ℰ d₁ | ℰcase→𝒞ℰ d₂
... | inj₁ lt1 | inj₁ lt2 = inj₁ (⊑-conj-L lt1 lt2)
... | inj₁ lt1 | inj₂ (u' , d₁' , cs') = inj₂ (u' , d₁' , cs-sub cs' (⊑-trans (⊔⊑⊔ lt1 ⊑-refl) (⊑-conj-L ⊑-bot ⊑-refl)))
... | inj₂ (u' , d₁' , cs') | inj₁ lt2 = inj₂ (u' , d₁' , cs-sub cs' (⊑-trans (⊔⊑⊔ ⊑-refl lt2) (⊑-conj-L ⊑-refl ⊑-bot)))
... | inj₂ (u' , d₁' , cs') | inj₂ (u'' , d₁'' , cs'') = inj₂ ((u' ⊔ u'') , ↓-⊔-intro d₁' d₁'' , cs-⊔ cs' cs'')
ℰcase→𝒞ℰ (↓-sub d x)
    with ℰcase→𝒞ℰ d 
... | inj₁ lt = inj₁ (⊑-trans x lt)
... | inj₂ (lit zero , d₁ , cs-Z x₁) = inj₂ (lit zero , d₁ , cs-Z (↓-sub x₁ x))
... | inj₂ (lit (suc n) , d₁ , cs-S x₁) = inj₂ (lit (suc n) , d₁ , cs-S (↓-sub x₁ x))
... | inj₂ (u ⊔ u₁ , d₁ , cs-⊔ cs cs₁) = inj₂ ((u ⊔ u₁) , d₁ ,  cs-sub (cs-⊔ cs cs₁) x)
... | inj₂ (u , d₁ , cs-sub cs lt) = inj₂ (u , d₁ , cs-sub cs (⊑-trans x lt))
ℰcase→𝒞ℰ (↓-case-Z d d₁) = inj₂ (lit zero , d , cs-Z d₁)
ℰcase→𝒞ℰ (↓-case-S {n = n} d d₁) = inj₂ (lit (suc n) , d , cs-S d₁)

CaseS→ℰcase : ∀ {Γ} {γ : Env Γ} {A} {L M} {N : Γ ▷ `ℕ ⊢ A} {u w}
  → γ ⊢ L ↓ u
  → CaseS (ℰ M) (ℰ N) γ u w
    ------------------------
  → ℰ (case L M N) γ w
CaseS→ℰcase d₁ (cs-Z x)      = ↓-case-Z d₁ x
CaseS→ℰcase d₁ (cs-S x)      = ↓-case-S d₁ x
CaseS→ℰcase d₁ (cs-⊔ cs cs₁) =
  ↓-⊔-intro (CaseS→ℰcase (↓-sub d₁ (⊑-conj-R1 ⊑-refl)) cs)
              (CaseS→ℰcase (↓-sub d₁ (⊑-conj-R2 ⊑-refl)) cs₁)
CaseS→ℰcase d₁ (cs-sub cs x) = ↓-sub (CaseS→ℰcase d₁ cs) x

𝒞ℰ→ℰcase : ∀ {Γ} {γ : Env Γ} {A} {L M} {N : Γ ▷ `ℕ ⊢ A} {v : Value A}
  → 𝒞 (ℰ L) (ℰ M) (ℰ N) γ v
    ------------------------
  → ℰ (case L M N) γ v
𝒞ℰ→ℰcase (inj₁ x) = ↓-sub ↓-⊥-intro x
𝒞ℰ→ℰcase (inj₂ (u , d , cs)) = CaseS→ℰcase d cs

case-equiv : ∀ {Γ A} {L M} {N : Γ ▷ `ℕ ⊢ A} → ℰ (case L M N) ≃ 𝒞 (ℰ L) (ℰ M) (ℰ N)
case-equiv γ v = ℰcase→𝒞ℰ , 𝒞ℰ→ℰcase

-- TODO μ

𝒰 : ∀ {Γ A} → Denotation (Γ ▷ A) A → Denotation Γ A
𝒰 D γ w = D (γ `, w) w

ℰμ→𝒰ℰ : ∀ {Γ} {γ : Env Γ} {A} {M : Γ ▷ A ⊢ A} {v : Value A}
  → ℰ (μ M) γ v
    ------------
  → 𝒰 (ℰ M) γ v
ℰμ→𝒰ℰ ↓-⊥-intro = ↓-⊥-intro
ℰμ→𝒰ℰ (↓-⊔-intro d₁ d₂) = {!!}
ℰμ→𝒰ℰ (↓-sub d x) = {!!}
ℰμ→𝒰ℰ (↓-μ d) = d

𝒰ℰ→ℰμ : ∀ {Γ} {γ : Env Γ} {A} {M : Γ ▷ A ⊢ A} {v : Value A}
  → 𝒰 (ℰ M) γ v
    ------------
  → ℰ (μ M) γ v
𝒰ℰ→ℰμ x = ↓-μ x

fix-equiv : ∀ {Γ A} {M : Γ ▷ A ⊢ A} → ℰ (μ M) ≃ 𝒰 (ℰ M)
fix-equiv γ v = ℰμ→𝒰ℰ , 𝒰ℰ→ℰμ
