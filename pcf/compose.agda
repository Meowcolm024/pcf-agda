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

data Case {Γ A} (D₂ : Denotation Γ A) (D₃ : Denotation (Γ ▷ `ℕ) A) (γ : Env Γ)
  : Value `ℕ → Value A → Set where

  cs-Z   : ∀ {w} → D₂ γ w → Case D₂ D₃ γ (lit zero) w

  cs-S   : ∀ {n w} → D₃ (γ `, lit n) w → Case D₂ D₃ γ (lit (suc n)) w

  cs-⊔   : ∀ {u u' w w'} → Case D₂ D₃ γ u w → Case D₂ D₃ γ u' w'
         → Case D₂ D₃ γ (u ⊔ u') (w ⊔ w')

  cs-sub : ∀ {u w v} → Case D₂ D₃ γ u w → v ⊑ w → Case D₂ D₃ γ u v
         
𝒞 : ∀ {Γ A} → Denotation Γ `ℕ → Denotation Γ A → Denotation (Γ ▷ `ℕ) A → Denotation Γ A
𝒞 D₁ D₂ D₃ γ w = w ⊑ ⊥ ⊎ (∃[ u ] (D₁ γ u × Case D₂ D₃ γ u w))

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

Case→ℰcase : ∀ {Γ} {γ : Env Γ} {A} {L M} {N : Γ ▷ `ℕ ⊢ A} {u w}
  → γ ⊢ L ↓ u
  → Case (ℰ M) (ℰ N) γ u w
    ------------------------
  → ℰ (case L M N) γ w
Case→ℰcase d₁ (cs-Z x)      = ↓-case-Z d₁ x
Case→ℰcase d₁ (cs-S x)      = ↓-case-S d₁ x
Case→ℰcase d₁ (cs-⊔ cs cs₁) =
  ↓-⊔-intro (Case→ℰcase (↓-sub d₁ (⊑-conj-R1 ⊑-refl)) cs)
              (Case→ℰcase (↓-sub d₁ (⊑-conj-R2 ⊑-refl)) cs₁)
Case→ℰcase d₁ (cs-sub cs x) = ↓-sub (Case→ℰcase d₁ cs) x

𝒞ℰ→ℰcase : ∀ {Γ} {γ : Env Γ} {A} {L M} {N : Γ ▷ `ℕ ⊢ A} {v : Value A}
  → 𝒞 (ℰ L) (ℰ M) (ℰ N) γ v
    ------------------------
  → ℰ (case L M N) γ v
𝒞ℰ→ℰcase (inj₁ x) = ↓-sub ↓-⊥-intro x
𝒞ℰ→ℰcase (inj₂ (u , d , cs)) = Case→ℰcase d cs

case-equiv : ∀ {Γ A} {L M} {N : Γ ▷ `ℕ ⊢ A} → ℰ (case L M N) ≃ 𝒞 (ℰ L) (ℰ M) (ℰ N)
case-equiv γ v = ℰcase→𝒞ℰ , 𝒞ℰ→ℰcase

data Fix {Γ A} (D : Denotation Γ (A ⇒ A)) (γ : Env Γ) : Value A → Set where
  fix-⊥   : Fix D γ ⊥
  fix-suc : ∀ {v w} → Fix D γ v → D γ (v ↦ w) → Fix D γ w
  fix-⊔   : ∀ {v w} → Fix D γ v → Fix D γ w → Fix D γ (v ⊔ w)
  fix-sub : ∀ {v w} → Fix D γ v → w ⊑ v → Fix D γ w

𝒰 : ∀ {Γ A} → Denotation Γ (A ⇒ A) → Denotation Γ A
𝒰 D γ w = Fix D γ w

ℰμ→𝒰ℰ : ∀ {Γ} {γ : Env Γ} {A} {M : Γ ⊢ A ⇒ A} {v}
  → ℰ (μ M) γ v
    ------------
  → 𝒰 (ℰ M) γ v
ℰμ→𝒰ℰ ↓-⊥-intro        = fix-⊥
ℰμ→𝒰ℰ (↓-⊔-intro d d₁) = fix-⊔ (ℰμ→𝒰ℰ d) (ℰμ→𝒰ℰ d₁)
ℰμ→𝒰ℰ (↓-sub d x)      = fix-sub (ℰμ→𝒰ℰ d) x
ℰμ→𝒰ℰ (↓-μ d d₁)       = fix-suc (ℰμ→𝒰ℰ d₁) d

𝒰ℰ→ℰμ : ∀ {Γ} {γ : Env Γ} {A} {M : Γ ⊢ A ⇒ A} {v}
  → 𝒰 (ℰ M) γ v
    ------------
  → ℰ (μ M) γ v
𝒰ℰ→ℰμ fix-⊥          = ↓-⊥-intro
𝒰ℰ→ℰμ (fix-suc x x₁) = ↓-μ x₁ (𝒰ℰ→ℰμ x)
𝒰ℰ→ℰμ (fix-⊔ x x₁)   = ↓-⊔-intro (𝒰ℰ→ℰμ x) (𝒰ℰ→ℰμ x₁)
𝒰ℰ→ℰμ (fix-sub x x₁) = ↓-sub (𝒰ℰ→ℰμ x) x₁

fix-equiv : ∀ {Γ A} {M : Γ ⊢ A ⇒ A} → ℰ (μ M) ≃ 𝒰 (ℰ M)
fix-equiv γ v = ℰμ→𝒰ℰ , 𝒰ℰ→ℰμ

open pcf.denote.≃-Reasoning

ℱ-cong : ∀ {Γ A B} {D D' : Denotation (Γ ▷ A) B}
  → D ≃ D'
    -----------
  → ℱ D ≃ ℱ D'
ℱ-cong {Γ} {A} {B} D≃D' γ v =
  (λ x → ℱ≃ {γ} {v} x D≃D') , (λ x → ℱ≃ {γ} {v} x (≃-sym D≃D'))
  where
  ℱ≃ : ∀ {γ : Env Γ} {v} {D D' : Denotation (Γ ▷ A) B}
    → ℱ D γ v  →  D ≃ D' → ℱ D' γ v
  ℱ≃ {v = ⊥} fd dd' = tt
  ℱ≃ {γ} {v ↦ w} fd dd' = proj₁ (dd' (γ `, v) w) fd
  ℱ≃ {γ} {u ⊔ w} fd dd' = ℱ≃ {γ} {u} (proj₁ fd) dd' , ℱ≃{γ}{w} (proj₂ fd) dd'

lam-cong : ∀ {Γ A B} {N N' : Γ ▷ A ⊢ B}
  → ℰ N ≃ ℰ N'
    -----------------
  → ℰ (ƛ N) ≃ ℰ (ƛ N')
lam-cong {N = N} {N'} N≃N' =
  start
    ℰ (ƛ N)
  ≃⟨ lam-equiv ⟩
    ℱ (ℰ N)
  ≃⟨ ℱ-cong N≃N' ⟩
    ℱ (ℰ N')
  ≃⟨ ≃-sym lam-equiv ⟩
    ℰ (ƛ N')
  ☐

●-cong : ∀ {Γ A B} {D₁ D₁' : Denotation Γ (A ⇒ B)} {D₂ D₂'}
  → D₁ ≃ D₁' → D₂ ≃ D₂'
    -----------------------
  → (D₁ ● D₂) ≃ (D₁' ● D₂')
●-cong {Γ} {A} {B} d1 d2 γ v =
  (λ x → ●≃ x d1 d2) , (λ x → ●≃ x (≃-sym d1) (≃-sym d2))
  where
  ●≃ : ∀ {γ : Env Γ} {v} {D₁ D₁' : Denotation Γ (A ⇒ B)} {D₂ D₂'}
    → (D₁ ● D₂) γ v  →  D₁ ≃ D₁'  →  D₂ ≃ D₂'
    → (D₁' ● D₂') γ v
  ●≃ (inj₁ v⊑⊥) eq₁ eq₂ = inj₁ v⊑⊥
  ●≃ {γ} {w} (inj₂ (v , Dv↦w , Dv)) eq₁ eq₂ =
    inj₂ (v , proj₁ (eq₁ γ (v ↦ w)) Dv↦w , proj₁ (eq₂ γ v) Dv)

app-cong : ∀ {Γ A B} {L L' : Γ ⊢ A ⇒ B} {M M'}
  → ℰ L ≃ ℰ L'
  → ℰ M ≃ ℰ M'
    -------------------------
   → ℰ (L · M) ≃ ℰ (L' · M')
app-cong {L = L} {L'} {M} {M'} L≅L' M≅M' =
  start
    ℰ (L · M)
  ≃⟨ app-equiv ⟩
    ℰ L ● ℰ M
  ≃⟨ ●-cong L≅L' M≅M' ⟩
    ℰ L' ● ℰ M'
  ≃⟨ ≃-sym app-equiv ⟩
    ℰ (L' · M')
  ☐

𝒮-cong : ∀ {Γ} {D D' : Denotation Γ `ℕ}
  → D ≃ D'
    -----------
  → 𝒮 D ≃ 𝒮 D'
𝒮-cong {Γ} {D} {D'} D≃D' γ v =
  (λ x → 𝒮≃ {γ} {v} x D≃D') , (λ x → 𝒮≃ {γ} {v} x (≃-sym D≃D'))
  where
  𝒮≃ : ∀ {γ : Env Γ} {v} {D D' : Denotation Γ `ℕ}
     → (𝒮 D) γ v → D ≃ D' → (𝒮 D') γ v
  𝒮≃ {γ} {⊥} sd dd' = tt
  𝒮≃ {γ} {lit (suc x)} sd dd' = dd' γ (lit x) .proj₁ sd
  𝒮≃ {γ} {v₁ ⊔ v₂} (sd₁ , sd₂) dd' = 𝒮≃ {γ} {v₁} sd₁ dd' , 𝒮≃ {γ} {v₂} sd₂ dd'

suc-cong : ∀ {Γ} {N N' : Γ ⊢ `ℕ}
  → ℰ N ≃ ℰ N'
    ---------------------
  → ℰ (`S N) ≃ ℰ (`S N')
suc-cong {N = N} {N'} N≃N' =
  start
    ℰ (`S N)
  ≃⟨ suc-equiv ⟩
    𝒮 (ℰ N)
  ≃⟨ 𝒮-cong N≃N' ⟩
    𝒮 (ℰ N')
  ≃⟨ ≃-sym suc-equiv ⟩
    ℰ (`S N')
  ☐

𝒞-cong : ∀ {Γ A} {D₁ D₁' D₂ D₂'} {D₃ D₃' : Denotation (Γ ▷ `ℕ) A}
  → D₁ ≃ D₁' → D₂ ≃ D₂' → D₃ ≃ D₃'
    -------------------------------
  → 𝒞 D₁ D₂ D₃ ≃ 𝒞 D₁' D₂' D₃'
𝒞-cong {Γ} {A} D₁≃D₁' D₂≃D₂' D₃≃D₃' γ v =
    (λ x → 𝒞≃ {γ} {v} x D₁≃D₁' D₂≃D₂' D₃≃D₃')
  , (λ x → 𝒞≃ {γ} {v} x (≃-sym D₁≃D₁') (≃-sym D₂≃D₂') (≃-sym D₃≃D₃'))
  where
  Case≃ : ∀ {γ : Env Γ} {v u} {D₂ D₂'} {D₃ D₃' : Denotation (Γ ▷ `ℕ) A}
    → Case D₂ D₃ γ u v → D₂ ≃ D₂' → D₃ ≃ D₃'
    → Case D₂' D₃' γ u v
  Case≃ {γ} {v} (cs-Z x) dd2 dd3 = cs-Z (dd2 γ v .proj₁ x)
  Case≃ {γ} {v} (cs-S x) dd2 dd3 = cs-S (dd3 (γ `, lit _) v .proj₁ x)
  Case≃ {γ} {v} (cs-⊔ cd cd₁) dd2 dd3 = cs-⊔ (Case≃ cd dd2 dd3) (Case≃ cd₁ dd2 dd3)
  Case≃ {γ} {v} (cs-sub cd x) dd2 dd3 = cs-sub (Case≃ cd dd2 dd3) x
    
  𝒞≃ : ∀ {γ : Env Γ} {v} {D₁ D₁' D₂ D₂'} {D₃ D₃' : Denotation (Γ ▷ `ℕ) A}
    → 𝒞 D₁ D₂ D₃ γ v → D₁ ≃ D₁' → D₂ ≃ D₂' → D₃ ≃ D₃'
    → 𝒞 D₁' D₂' D₃' γ v
  𝒞≃ {γ} {v} (inj₁ x) dd1 dd2 dd3 = inj₁ x
  𝒞≃ {γ} {v} (inj₂ (u , d' , cs)) dd1 dd2 dd3 =
    inj₂ (u , dd1 γ u .proj₁ d' , Case≃ cs dd2 dd3) 

case-cong : ∀ {Γ A} {L L' M M'} {N N' : Γ ▷ `ℕ ⊢ A}
  → ℰ L ≃ ℰ L'
  → ℰ M ≃ ℰ M'
  → ℰ N ≃ ℰ N'
    ----------------------------------
  → ℰ (case L M N) ≃ ℰ (case L' M' N')
case-cong {L = L} {L'} {M} {M'} {N} {N'} L≃L' M≃M' N≃N' =
  start
    ℰ (case L M N)
  ≃⟨ case-equiv ⟩
    𝒞 (ℰ L) (ℰ M) (ℰ N)
  ≃⟨ 𝒞-cong L≃L' M≃M' N≃N' ⟩
    𝒞 (ℰ L') (ℰ M') (ℰ N')
  ≃⟨ ≃-sym case-equiv ⟩
    ℰ (case L' M' N')
  ☐ 

𝒰-cong : ∀ {Γ A} {D D' : Denotation Γ (A ⇒ A)}
  → D ≃ D'
    -----------
  → 𝒰 D ≃ 𝒰 D'
𝒰-cong {Γ} {A} D≃D' γ v =
  (λ x → 𝒰≃ {γ} {v} x D≃D') , (λ x → 𝒰≃ {γ} {v} x (≃-sym D≃D'))
  where
  𝒰≃ : ∀ {γ : Env Γ} {v} {D D' : Denotation Γ (A ⇒ A)}
    → 𝒰 D γ v  →  D ≃ D' → 𝒰 D' γ v
  𝒰≃ {γ} {v} fix-⊥ dd' = fix-⊥
  𝒰≃ {γ} {v} (fix-suc ud x) dd' = fix-suc (𝒰≃ ud dd') (dd' γ (_ ↦ v) .proj₁ x)
  𝒰≃ {γ} {v} (fix-⊔ ud ud₁) dd' = fix-⊔ (𝒰≃ ud dd') (𝒰≃ ud₁ dd')
  𝒰≃ {γ} {v} (fix-sub ud x) dd' = fix-sub (𝒰≃ ud dd') x

fix-cong : ∀ {Γ A} {N N' : Γ ⊢ A ⇒ A}
  → ℰ N ≃ ℰ N'
    -----------------
  → ℰ (μ N) ≃ ℰ (μ N')
fix-cong {N = N} {N'} N≃N' =
  start
    ℰ (μ N)
  ≃⟨ fix-equiv ⟩
    𝒰 (ℰ N)
  ≃⟨ 𝒰-cong N≃N' ⟩
    𝒰 (ℰ N')
  ≃⟨ ≃-sym fix-equiv ⟩
    ℰ (μ N')
  ☐
