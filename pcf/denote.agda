module pcf.denote where

open import pcf.base
open import pcf.subst

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_)
open import Relation.Nullary.Negation using (¬_; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Value : Ty → Set where
  ⊥   : ∀ {A} → Value A
  lit : ℕ → Value `ℕ
  _↦_ : ∀ {A B} → Value A → Value B → Value (A ⇒ B)
  _⊔_ : ∀ {A} → Value A → Value A → Value A

infix 2 _⊑_

data _⊑_ : ∀ {A} → Value A → Value A → Set where
  ⊑-bot     : ∀ {A} {v : Value A} → ⊥ ⊑ v
  ⊑-lit     : ∀ {n} → lit n ⊑ lit n
  ⊑-conj-L  : ∀ {A} {u v w : Value A} → v ⊑ u → w ⊑ u → v ⊔ w ⊑ u
  ⊑-conj-R1 : ∀ {A} {u v w : Value A} → u ⊑ v → u ⊑ v ⊔ w
  ⊑-conj-R2 : ∀ {A} {u v w : Value A} → u ⊑ w → u ⊑ v ⊔ w
  ⊑-trans   : ∀ {A} {u v w : Value A} → u ⊑ v → v ⊑ w → u ⊑ w
  ⊑-fun     : ∀ {A B} {v v' : Value A} {w w' : Value B}
    → v' ⊑ v → w ⊑ w' → (v ↦ w) ⊑ (v' ↦ w')
  ⊑-dist    : ∀ {A B} {v : Value A} {w w' : Value B}
    → v ↦ (w ⊔ w') ⊑ (v ↦ w) ⊔ (v ↦ w')

⊑-refl : ∀ {A} {v : Value A} → v ⊑ v
⊑-refl {v = ⊥} = ⊑-bot
⊑-refl {v = lit n} = ⊑-lit
⊑-refl {v = v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v = v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)

⊔⊑⊔ : ∀ {A} {v w v′ w′ : Value A}
  → v ⊑ v′  →  w ⊑ w′
    -----------------------
  → (v ⊔ w) ⊑ (v′ ⊔ w′)
⊔⊑⊔ d₁ d₂ = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)

⊔↦⊔-dist : ∀ {A B} {v v′ : Value A} {w w′ : Value B}
  → (v ⊔ v′) ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v′ ↦ w′)
⊔↦⊔-dist = ⊑-trans ⊑-dist (⊔⊑⊔ (⊑-fun (⊑-conj-R1 ⊑-refl) ⊑-refl)
                            (⊑-fun (⊑-conj-R2 ⊑-refl) ⊑-refl))

⊔⊑-invL : ∀ {A} {u v w : Value A}
  → u ⊔ v ⊑ w
    ---------
  → u ⊑ w
⊔⊑-invL (⊑-conj-L lt1 lt2) = lt1
⊔⊑-invL (⊑-conj-R1 lt) = ⊑-conj-R1 (⊔⊑-invL lt)
⊔⊑-invL (⊑-conj-R2 lt) = ⊑-conj-R2 (⊔⊑-invL lt)
⊔⊑-invL (⊑-trans lt1 lt2) = ⊑-trans (⊔⊑-invL lt1) lt2

⊔⊑-invR : ∀ {A} {u v w : Value A}
  → u ⊔ v ⊑ w
    ---------
  → v ⊑ w
⊔⊑-invR (⊑-conj-L lt1 lt2) = lt2
⊔⊑-invR (⊑-conj-R1 lt) = ⊑-conj-R1 (⊔⊑-invR lt)
⊔⊑-invR (⊑-conj-R2 lt) = ⊑-conj-R2 (⊔⊑-invR lt)
⊔⊑-invR (⊑-trans lt1 lt2) = ⊑-trans (⊔⊑-invR lt1) lt2

Env : Ctx → Set
Env Γ = ∀ {A} → Γ ∋ A → Value A

`∅ : Env ∅
`∅ ()

infixl 5 _`,_

_`,_ : ∀ {Γ A} → Env Γ → Value A → Env (Γ ▷ A)
(γ `, v) Z = v
(γ `, v) (S x) = γ x

init : ∀ {Γ A} → Env (Γ ▷ A) → Env Γ
init γ x = γ (S x)

last : ∀ {Γ A} → Env (Γ ▷ A) → Value A
last γ = γ Z

init-last : ∀ {Γ A} → (γ : Env (Γ ▷ A)) → γ ≡ (init γ `, last γ)
init-last {Γ} {A} γ = extensionality lemma
  where lemma : ∀ (x : Γ ▷ A ∋ A) → γ x ≡ (init γ `, last γ) x
        lemma Z      =  refl
        lemma (S x)  =  refl

_`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
_`⊑_ {Γ} γ δ = ∀ {A} (x : Γ ∋ A) → γ x ⊑ δ x

`⊥ : ∀ {Γ} → Env Γ
`⊥ x = ⊥

_`⊔_ : ∀ {Γ} → Env Γ → Env Γ → Env Γ
(γ `⊔ δ) x = γ x ⊔ δ x

`⊑-refl : ∀ {Γ} {γ : Env Γ} → γ `⊑ γ
`⊑-refl {Γ} {γ} x = ⊑-refl {v = γ x}

⊑-env-conj-R1 : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
⊑-env-conj-R1 γ δ x = ⊑-conj-R1 ⊑-refl

⊑-env-conj-R2 : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
⊑-env-conj-R2 γ δ x = ⊑-conj-R2 ⊑-refl

infix  2 _⊢_↓_

data _⊢_↓_ : ∀ {Γ A} → Env Γ → Γ ⊢ A → Value A → Set where

  ↓-var : ∀ {Γ A} {γ : Env Γ} {x : Γ ∋ A}
      --------------
    → γ ⊢ ` x ↓ γ x

  ↓-↦-elim : ∀ {Γ A B} {γ : Env Γ} {L : Γ ⊢ A ⇒ B} {M v w}
    → γ ⊢ L ↓ (v ↦ w)
    → γ ⊢ M ↓ v
      --------------
    → γ ⊢ L · M ↓ w

  ↓-↦-intro : ∀ {Γ A B} {γ : Env Γ} {N : Γ ▷ A ⊢ B} {v w}
    → (γ `, v) ⊢ N ↓ w
      ------------------
    → γ ⊢ ƛ N ↓ (v ↦ w)

  ↓-⊥-intro : ∀ {Γ A} {γ : Env Γ} {M : Γ ⊢ A}
      ----------
    → γ ⊢ M ↓ ⊥

  ↓-⊔-intro : ∀ {Γ A} {γ : Env Γ} {M : Γ ⊢ A} {v w}
    → γ ⊢ M ↓ v
    → γ ⊢ M ↓ w
      ----------------
    → γ ⊢ M ↓ (v ⊔ w)

  ↓-sub : ∀ {Γ A} {γ : Env Γ} {M : Γ ⊢ A} {v w}
    → γ ⊢ M ↓ v
    → w ⊑ v
      ----------
    → γ ⊢ M ↓ w

  ↓-Z : ∀ {Γ} {γ : Env Γ}
      --------------------
    → γ ⊢ `Z ↓ lit zero

  ↓-S : ∀ {Γ} {γ : Env Γ} {M n}
    → γ ⊢ M ↓ lit n
      -----------------------
    → γ ⊢ `S M ↓ lit (suc n)

  ↓-case-Z : ∀ {Γ A} {γ : Env Γ} {L : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N v}
    → γ ⊢ L ↓ lit zero
    → γ ⊢ M ↓ v
      -------------------
    → γ ⊢ case L M N ↓ v

  ↓-case-S : ∀ {Γ A} {γ : Env Γ} {L} {M : Γ ⊢ A} {N v n}
    → γ ⊢ L ↓ lit (suc n)
    → (γ `, lit n) ⊢ N ↓ v
      ---------------------
    → γ ⊢ case L M N ↓ v

  ↓-μ : ∀ {Γ A} {γ : Env Γ} {N : Γ ▷ A ⊢ A} {v}
    → (γ `, v) ⊢ N ↓ v
      -----------------
    → γ ⊢ μ N ↓ v

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

Denotation : Ctx → Ty → Set₁
Denotation Γ A = Env Γ → Value A → Set

ℰ : ∀{Γ A} → (M : Γ ⊢ A) → Denotation Γ A
ℰ M = λ γ v → γ ⊢ M ↓ v

infix 3 _≃_

_≃_ : ∀ {Γ A} → (Denotation Γ A) → (Denotation Γ A) → Set
_≃_ {Γ} {A} D₁ D₂ = (γ : Env Γ) → (v : Value A) → D₁ γ v iff D₂ γ v

≃-refl : ∀ {Γ A} → {M : Denotation Γ A}
  → M ≃ M
≃-refl γ v = (λ x → x) , (λ x → x)

≃-sym : ∀ {Γ A} → {M N : Denotation Γ A}
  → M ≃ N
    -----
  → N ≃ M
≃-sym eq γ v = (proj₂ (eq γ v)) , (proj₁ (eq γ v))

≃-trans : ∀ {Γ A} → {M₁ M₂ M₃ : Denotation Γ A}
  → M₁ ≃ M₂
  → M₂ ≃ M₃
    -------
  → M₁ ≃ M₃
≃-trans eq1 eq2 γ v = (λ z → proj₁ (eq2 γ v) (proj₁ (eq1 γ v) z))
                    , (λ z → proj₂ (eq1 γ v) (proj₂ (eq2 γ v) z))

module ≃-Reasoning {Γ A} where

  infix  1 start_
  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _☐

  start_ : ∀ {x y : Denotation Γ A}
    → x ≃ y
      -----
    → x ≃ y
  start x≃y  =  x≃y

  _≃⟨_⟩_ : ∀ (x : Denotation Γ A) {y z : Denotation Γ A}
    → x ≃ y
    → y ≃ z
      -----
    → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) =  ≃-trans x≃y y≃z

  _≃⟨⟩_ : ∀ (x : Denotation Γ A) {y : Denotation Γ A}
    → x ≃ y
      -----
    → x ≃ y
  x ≃⟨⟩ x≃y  =  x≃y

  _☐ : ∀ (x : Denotation Γ A)
      -----
    → x ≃ x
  (x ☐)  =  ≃-refl

lift-⊑ : ∀ {Γ Δ A} {v : Value A} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Ren Γ Δ)
  → γ `⊑ (δ ∘ ρ)
    --------------------------------
  → (γ `, v) `⊑ ((δ `, v) ∘ lift ρ)
lift-⊑ ρ lt Z = ⊑-refl
lift-⊑ ρ lt (S n′) = lt n′

ren-pres : ∀ {Γ Δ A} {v : Value A} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ A}
  → (ρ : Ren Γ Δ)
  → γ `⊑ (δ ∘ ρ)
  → γ ⊢ M ↓ v
    ------------------
  → δ ⊢ (ren ρ M) ↓ v
ren-pres ρ lt (↓-var {x = x}) = ↓-sub ↓-var (lt x)
ren-pres ρ lt (↓-↦-elim d d₁) =
  ↓-↦-elim (ren-pres ρ lt d) (ren-pres ρ lt d₁)
ren-pres ρ lt (↓-↦-intro d) =
  ↓-↦-intro (ren-pres (lift ρ) (lift-⊑ ρ lt) d)
ren-pres ρ lt ↓-⊥-intro = ↓-⊥-intro
ren-pres ρ lt (↓-⊔-intro d d₁) =
  ↓-⊔-intro (ren-pres ρ lt d) (ren-pres ρ lt d₁)
ren-pres ρ lt (↓-sub d x) = ↓-sub (ren-pres ρ lt d) x
ren-pres ρ lt ↓-Z = ↓-Z
ren-pres ρ lt (↓-S d) = ↓-S (ren-pres ρ lt d)
ren-pres ρ lt (↓-case-Z d d₁) =
  ↓-case-Z (ren-pres ρ lt d) (ren-pres ρ lt d₁)
ren-pres ρ lt (↓-case-S d d₁) =
  ↓-case-S (ren-pres ρ lt d) (ren-pres (lift ρ) (lift-⊑ ρ lt) d₁)
ren-pres ρ lt (↓-μ d) =
  ↓-μ (ren-pres (lift ρ) (lift-⊑ ρ lt) d)

⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {A} {M : Γ ⊢ A} {v}
  → γ ⊢ M ↓ v
  → γ `⊑ δ
    ----------
  → δ ⊢ M ↓ v
⊑-env{Γ} {γ} {δ} {A} {M} {v} d lt
      with ren-pres {Γ} {Γ} {A} {v} {γ} {δ} {M} id lt d
... | δ⊢id[M]↓v rewrite ren-id {Γ} {A} {M} =
      δ⊢id[M]↓v

up-env : ∀ {Γ} {γ : Env Γ} {A B} {M : Γ ▷ B ⊢ A} {v u₁ u₂}
  → (γ `, u₁) ⊢ M ↓ v
  → u₁ ⊑ u₂
    -----------------
  → (γ `, u₂) ⊢ M ↓ v
up-env d lt = ⊑-env d (ext-le lt)
  where
  ext-le : ∀ {Γ A} {γ : Env Γ} {u₁ u₂ : Value A}
         → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
  ext-le lt Z = lt
  ext-le lt (S n) = ⊑-refl

infix 5 _∈_

_∈_ : ∀ {A} → Value A → Value A → Set
u ∈ ⊥       = u ≡ ⊥
u ∈ lit n   = u ≡ lit n
u ∈ v ↦ w   = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w

infix 5 _⊆_

_⊆_ : ∀ {A} → Value A → Value A → Set
v ⊆ w = ∀ {u} → u ∈ v → u ∈ w

∈→⊑ : ∀ {A} {u v : Value A}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {u = .⊥}    {⊥}     refl     = ⊑-bot
∈→⊑ {u = lit n} {lit n} refl     = ⊑-lit
∈→⊑ {u = v ↦ w} {v ↦ w} refl     = ⊑-refl
∈→⊑ {u = u}     {v ⊔ w} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u = u}     {v ⊔ w} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)

⊆→⊑ : ∀ {A} {u v : Value A}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {u = ⊥} s with s {⊥} refl
... | x = ⊑-bot
⊆→⊑ {u = lit n} s with s {lit n} refl
... | x = ∈→⊑ x
⊆→⊑ {u = u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u = u ⊔ u′} s
  = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))

⊔⊆-inv : ∀ {A} {u v w : Value A}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x))

↦⊆→∈ : ∀ {A B} {v w} {u : Value (A ⇒ B)}
     → v ↦ w ⊆ u
       ---------
     → v ↦ w ∈ u
↦⊆→∈ incl = incl refl

data Fun : ∀ {A} → Value A → Set where
  fun : ∀ {A B} {u : Value (A ⇒ B)} {v w}
      → u ≡ (v ↦ w) → Fun u

all-funs : ∀ {A B} → Value (A ⇒ B) → Set
all-funs v = ∀ {u} → u ∈ v → Fun u

¬Fun⊥ : ∀ {A} → ¬ (Fun {A} ⊥)
¬Fun⊥ {A ⇒ B} (fun ())

all-funs∈ : ∀ {A B} {u : Value (A ⇒ B)}
      → all-funs u
      → Σ[ v ∈ Value A ] Σ[ w ∈ Value B ] v ↦ w ∈ u
all-funs∈ {u = ⊥} f with f {⊥} refl
... | fun ()
all-funs∈ {u = v ↦ w} f = v , w , refl
all-funs∈ {u = u ⊔ u'} f with all-funs∈ (λ z → f (inj₁ z))
... |  v ,  w , m = v , w , inj₁ m

⨆dom : ∀ {A B} → (u : Value (A ⇒ B)) → Value A
⨆dom ⊥        = ⊥
⨆dom (v ↦ w)  = v
⨆dom (u ⊔ u′) = ⨆dom u ⊔ ⨆dom u′

⨆cod : ∀ {A B} → (u : Value (A ⇒ B)) → Value B
⨆cod ⊥        = ⊥
⨆cod (v ↦ w)  = w
⨆cod (u ⊔ u′) = ⨆cod u ⊔ ⨆cod u′

↦∈→⊆⨆dom : ∀ {A B} {u : Value (A ⇒ B)} {v w}
          → all-funs u  →  (v ↦ w) ∈ u
            ---------------------------
          → v ⊆ ⨆dom u
↦∈→⊆⨆dom {u = v ↦ w}  fg refl     z = z
↦∈→⊆⨆dom {u = u ⊔ u'} fg (inj₁ x) z =
  inj₁ (↦∈→⊆⨆dom (λ {u = u₂} z₁ → fg (inj₁ z₁)) x z)
↦∈→⊆⨆dom {u = u ⊔ u'} fg (inj₂ y) z =
  inj₂ (↦∈→⊆⨆dom (λ {u = u₂} z₁ → fg (inj₂ z₁)) y z)

⊆↦→⨆cod⊆ : ∀ {A B} {u : Value (A ⇒ B)} {v w}
        → u ⊆ v ↦ w
          ----------
        → ⨆cod u ⊆ w
⊆↦→⨆cod⊆ {u = ⊥} s refl with s {⊥} refl
... | ()
⊆↦→⨆cod⊆ {u = v ↦ w} s m with s {v ↦ w} refl
... | refl = m
⊆↦→⨆cod⊆ {u = u ⊔ u'} s (inj₁ x) = ⊆↦→⨆cod⊆ (λ z → s (inj₁ z)) x
⊆↦→⨆cod⊆ {u = u ⊔ u'} s (inj₂ y) = ⊆↦→⨆cod⊆ (λ z → s (inj₂ z)) y

factor : ∀ {A B} → (u u' : Value (A ⇒ B)) → (v : Value A) → (w : Value B) → Set
factor u u' v w = (all-funs u') × (u' ⊆ u) × (⨆dom u' ⊑ v) × (w ⊑ ⨆cod u')

sub-inv-trans : ∀ {A B} {u' u₂ u : Value (A ⇒ B)}
    → all-funs u' → u' ⊆ u
    → (∀ {v' w'} → v' ↦ w' ∈ u → Σ[ u₃ ∈ Value (A ⇒ B) ] factor u₂ u₃ v' w')
      -----------------------------------------------------------------------
    → Σ[ u₃ ∈ Value (A ⇒ B) ] factor u₂ u₃ (⨆dom u') (⨆cod u')
sub-inv-trans {u' = ⊥} {u₂} {u} fg u'⊆u IH = contradiction (fg refl) ¬Fun⊥
sub-inv-trans {u' = u' ↦ u''} {u₂} {u} fg u'⊆u IH = IH (u'⊆u refl)
sub-inv-trans {u' = u₁' ⊔ u₂'} {u₂} {u} fg u'⊆u IH
    with ⊔⊆-inv u'⊆u
... | u₁'⊆u , u₂'⊆u
    with sub-inv-trans {u' = u₁'} {u₂} {u} (λ z → fg (inj₁ z)) u₁'⊆u IH
       | sub-inv-trans {u' = u₂'} {u₂} {u} (λ z → fg (inj₂ z)) u₂'⊆u IH
... | u₃₁ , fu21' , u₃₁⊆u₂ , du₃₁⊑du₁' , cu₁'⊑cu₃₁
    | u₃₂ , fu22' , u₃₂⊆u₂ , du₃₂⊑du₂' , cu₁'⊑cu₃₂ =
     (u₃₁ ⊔ u₃₂) , fu₂' , u₂'⊆u₂ ,
      ⊔⊑⊔ du₃₁⊑du₁' du₃₂⊑du₂' ,
        ⊔⊑⊔ cu₁'⊑cu₃₁ cu₁'⊑cu₃₂
    where fu₂' : {v' : Value _} → v' ∈ u₃₁ ⊎ v' ∈ u₃₂ → Fun v'
          fu₂' {v'} (inj₁ x) = fu21' x
          fu₂' {v'} (inj₂ y) = fu22' y
          u₂'⊆u₂ : {C : Value _} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
          u₂'⊆u₂ {C} (inj₁ x) = u₃₁⊆u₂ x
          u₂'⊆u₂ {C} (inj₂ y) = u₃₂⊆u₂ y

sub-inv : ∀ {A B} {u₁ u₂ : Value (A ⇒ B)}
        → u₁ ⊑ u₂
        → ∀{v w} → v ↦ w ∈ u₁
          -------------------------------------
        → Σ[ u₃ ∈ Value _ ] factor u₂ u₃ v w
sub-inv {u₁ = ⊥} {u₂} lt {v} {w} ()
sub-inv {u₁ = u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₁ x) = sub-inv lt1 x
sub-inv {u₁ = u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₂ y) = sub-inv lt2 y
sub-inv {u₁ = u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R1 lt) {v} {w} m
    with sub-inv lt m
... | u₃₁ , fu₃₁ , u₃₁⊆u₂₁ , domu₃₁⊑v , w⊑codu₃₁ =
      u₃₁ , fu₃₁ , (λ {w} z → inj₁ (u₃₁⊆u₂₁ z)) , domu₃₁⊑v , w⊑codu₃₁
sub-inv {u₁ = u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R2 lt) {v} {w} m
    with sub-inv lt m
... | u₃₂ , fu₃₂ , u₃₂⊆u₂₂ , domu₃₂⊑v , w⊑codu₃₂ =
      u₃₂ , fu₃₂ , (λ {C} z → inj₂ (u₃₂⊆u₂₂ z)) , domu₃₂⊑v , w⊑codu₃₂
sub-inv {u₁ = u₁} {u₂} (⊑-trans{v = u} u₁⊑u u⊑u₂) {v} {w} v↦w∈u₁
    with sub-inv u₁⊑u v↦w∈u₁
... | u' , fu' , u'⊆u , domu'⊑v , w⊑codu'
    with sub-inv-trans {u' = u'} fu' u'⊆u (sub-inv u⊑u₂)
... | u₃ , fu₃ , u₃⊆u₂ , domu₃⊑domu' , codu'⊑codu₃ =
      u₃ , fu₃ , u₃⊆u₂ , ⊑-trans domu₃⊑domu' domu'⊑v , ⊑-trans w⊑codu' codu'⊑codu₃
sub-inv {u₁ = u₁₁ ↦ u₁₂} {u₂₁ ↦ u₂₂} (⊑-fun lt1 lt2) refl =
    u₂₁ ↦ u₂₂ , (λ {w} → fun) , (λ z → z) , lt1 , lt2
sub-inv {u₁ = u₂₁ ↦ (u₂₂ ⊔ u₂₃)} {(u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃)} ⊑-dist
    {.u₂₁} {.(u₂₂ ⊔ u₂₃)} refl =
    (u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃) , f , g , ⊑-conj-L ⊑-refl ⊑-refl , ⊑-refl
  where f : all-funs ((u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃))
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : ((u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃)) ⊆ ((u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃))
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y

sub-inv-fun : ∀ {A B} {v w} {u₁ : Value (A ⇒ B)}
    → (v ↦ w) ⊑ u₁
      -------------------------------------------------
    → Σ[ u₂ ∈ Value (A ⇒ B) ] all-funs u₂ × (u₂ ⊆ u₁)
         × (∀{v′ w′} → (v′ ↦ w′) ∈ u₂ → v′ ⊑ v) × (w ⊑ ⨆cod u₂)
sub-inv-fun {v = v} {w} {u₁} abc
    with sub-inv abc {v} {w} refl
... | u₂ , f , u₂⊆u₁ , db , cc = u₂ , f , u₂⊆u₁ , G , cc
   where G : ∀ {D E} → (D ↦ E) ∈ u₂ → D ⊑ v
         G {D}{E} m = ⊑-trans (⊆→⊑ (↦∈→⊆⨆dom f m)) db

↦⊑↦-inv : ∀ {A B} {v v' : Value A} {w w' : Value B}
        → v ↦ w ⊑ v' ↦ w'
          --------------------
        → (v' ⊑ v) × (w ⊑ w')
↦⊑↦-inv {v = v} {v'} {w} {w′} lt
    with sub-inv-fun lt
... | Γ , f , Γ⊆v34 , lt1 , lt2
    with all-funs∈ f
... | u ,  u' , u↦u'∈Γ
    with Γ⊆v34 u↦u'∈Γ
... | refl = lt1 u↦u'∈Γ , ⊑-trans lt2 (⊆→⊑ (⊆↦→⨆cod⊆ Γ⊆v34))

data Lit : ∀ {A} → Value A → Set where
  lit : ∀ {u : Value `ℕ} {n} → u ≡ (lit n) → Lit u

all-lits : Value `ℕ → Set
all-lits v = ∀ {u} → u ∈ v → Lit u

¬Lit⊥ : ∀ {A} → ¬ (Lit {A} ⊥)
¬Lit⊥ {`ℕ} (lit ())

all-lits∈ : ∀ {u : Value `ℕ}
      → all-lits u
      → ∃[ n ] lit n ∈ u
all-lits∈ {⊥} f with f {⊥} refl
... | lit ()
all-lits∈ {lit x} f = x , refl
all-lits∈ {u ⊔ u'} f with all-lits∈ (λ z → f (inj₁ z))
... | v , w = v , inj₁ w

-- ⨆lit : (u : Value `ℕ) → Value `ℕ
-- ⨆lit ⊥ = ⊥
-- ⨆lit (lit x) = lit x
-- ⨆lit (u ⊔ u') = ⨆lit u ⊔ ⨆lit u'

literal : (u u' v : Value `ℕ) → Set
literal u u' v = all-lits u' × (u' ⊆ u) × (v ≡ u')

sub-inv-trans-literal : ∀ {u' u₂ u : Value `ℕ}
    → all-lits u'  →  u' ⊆ u
    → (∀{n} → lit n ∈ u → ∃[ u₃ ] literal u₂ u₃ (lit n))
      ---------------------------------------------------
    → ∃[ u₃ ] literal u₂ u₃ u'
sub-inv-trans-literal {u' = ⊥} {u₂} {u} lu' u'⊆u IH = contradiction (lu' refl) ¬Lit⊥
sub-inv-trans-literal {u' = lit x} {u₂} {u} lu' u'⊆u IH = IH (u'⊆u refl)
sub-inv-trans-literal {u' = u₁' ⊔ u₂'} {u₂} {u} lg u'⊆u IH
    with ⊔⊆-inv u'⊆u
... | u₁'⊆u , u₂'⊆u
    with sub-inv-trans-literal {u' = u₁'} {u₂} {u} (λ z → lg (inj₁ z)) u₁'⊆u IH
       | sub-inv-trans-literal {u' = u₂'} {u₂} {u} (λ z → lg (inj₂ z)) u₂'⊆u IH
... | u₃₁ , lu21' , u₃₁⊆u₂ , eq1
    | u₃₂ , lu22' , u₃₂⊆u₂ , eq2
    = (u₃₁ ⊔ u₃₂) , lu2' , u₂'⊆u₂ , Eq.cong₂ _⊔_ eq1 eq2
    where
      lu2' : ∀ {v' : Value `ℕ} → v' ∈ u₃₁ ⊎ v' ∈ u₃₂ → Lit v'
      lu2' (inj₁ x) = lu21' x
      lu2' (inj₂ y) = lu22' y
      u₂'⊆u₂ : ∀ {C : Value `ℕ} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
      u₂'⊆u₂ (inj₁ x) = u₃₁⊆u₂ x
      u₂'⊆u₂ (inj₂ y) = u₃₂⊆u₂ y

sub-inv-literal : ∀ {u₁ u₂ : Value `ℕ}
    → u₁ ⊑ u₂
    → ∀{n} → lit n ∈ u₁
      ------------------------------
    → ∃[ u₃ ] literal u₂ u₃ (lit n)
sub-inv-literal {u₁ = lit x} {u₂} ⊑-lit {n} refl = lit x , (λ {u} → lit) , (λ {u} z → z) , refl
sub-inv-literal {u₁ = u₁ ⊔ u₃} {u₂} (⊑-conj-L lt lt₁) {n} (inj₁ x) = sub-inv-literal lt x
sub-inv-literal {u₁ = u₁ ⊔ u₃} {u₂} (⊑-conj-L lt lt₁) {n} (inj₂ y) = sub-inv-literal lt₁ y
sub-inv-literal {u₁ = u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R1 lt) {n} m
    with sub-inv-literal lt m
... | u₃₁ , lu₃₁ , u₃₁⊆u₂₁ , lit⊑u₃₁
    = u₃₁ , lu₃₁ , (λ {u} z → inj₁ (u₃₁⊆u₂₁ z)) , lit⊑u₃₁
sub-inv-literal {u₁ = u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R2 lt) {n} m
    with sub-inv-literal lt m
... | u₃₂ , lu₃₂ , u₃₂⊆u₂₂ , lit⊑u₃₂
  = u₃₂ , lu₃₂ , (λ {u} z → inj₂ (u₃₂⊆u₂₂ z)) , lit⊑u₃₂
sub-inv-literal {u₁ = u₁} {u₂} (⊑-trans {v = u} lt lt₁) {n} m
    with sub-inv-literal lt m
... | u' , lu' , u'⊆u , lit≡u'
    with sub-inv-trans-literal {u' = u'} lu' u'⊆u (sub-inv-literal lt₁)
... | u₃ , lu₃ , u₃⊆u₂ , u'≡u₃ = u₃ , lu₃ , u₃⊆u₂ , Eq.trans lit≡u' u'≡u₃

sub-inv-lit : ∀ {u₁ : Value `ℕ} {n}
    → (lit n) ⊑ u₁
      ----------------------------------------------------
    → ∃[ u₂ ] all-lits u₂ × (u₂ ⊆ u₁) × (lit n ≡ u₂)
sub-inv-lit {u₁ = u₁} {n} abc = sub-inv-literal abc {n} refl

all-lits-⊔ : ∀ {u u' : Value `ℕ} → all-lits u → all-lits u' → all-lits (u ⊔ u')
all-lits-⊔ {u} {u'} al al' (inj₁ x) = al x
all-lits-⊔ {u} {u'} al al' (inj₂ y) = al' y
