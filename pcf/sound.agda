module pcf.sound where

open import pcf.base
open import pcf.subst
open import pcf.denote
open import pcf.compose

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to bot)
open import Function.Base using (id; _∘_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

infix 3 _`⊢_↓_

_`⊢_↓_ : ∀ {Δ Γ} → Env Δ → Sub Γ Δ → Env Γ → Set
_`⊢_↓_ {Δ} {Γ} δ σ γ = (∀ {A} (x : Γ ∋ A) → δ ⊢ σ x ↓ γ x)

sub-lift : ∀ {Γ Δ A} {v : Value A} {γ : Env Γ} {δ : Env Δ}
  → (σ : Sub Γ Δ)
  → δ `⊢ σ ↓ γ
   ----------------------------
  → δ `, v `⊢ lifts σ ↓ γ `, v
sub-lift σ d Z      = ↓-var
sub-lift σ d (S x′) = ren-pres S (λ _ → ⊑-refl) (d x′)

sub-pres : ∀ {Γ Δ A v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ A}
  → (σ : Sub Γ Δ)
  → δ `⊢ σ ↓ γ
  → γ ⊢ M ↓ v
    ------------------
  → δ ⊢ sub σ M ↓ v
sub-pres σ s (↓-var {x = x})  = s x
sub-pres σ s (↓-↦-elim d d₁)  = ↓-↦-elim (sub-pres σ s d) (sub-pres σ s d₁)
sub-pres σ s (↓-↦-intro d)    = ↓-↦-intro (sub-pres (lifts σ) (sub-lift σ s) d)
sub-pres σ s ↓-⊥-intro        = ↓-⊥-intro
sub-pres σ s (↓-⊔-intro d d₁) = ↓-⊔-intro (sub-pres σ s d) (sub-pres σ s d₁)
sub-pres σ s (↓-sub d x)      = ↓-sub (sub-pres σ s d) x
sub-pres σ s ↓-Z              = ↓-Z
sub-pres σ s (↓-S d)          = ↓-S (sub-pres σ s d)
sub-pres σ s (↓-case-Z d d₁)  = ↓-case-Z (sub-pres σ s d) (sub-pres σ s d₁)
sub-pres σ s (↓-case-S d d₁)  = ↓-case-S (sub-pres σ s d) (sub-pres (lifts σ) (sub-lift σ s) d₁)
sub-pres σ s (↓-μ d d₁)       = ↓-μ (sub-pres σ s d) (sub-pres σ s d₁)

substitution : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B} {M v w}
   → γ `, v ⊢ N ↓ w
   → γ ⊢ M ↓ v
     ---------------
   → γ ⊢ N [ M ] ↓ w
substitution {M = M} dn dm = sub-pres (sub-zero M) (λ { Z → dm ; (S x) → ↓-var }) dn

lit⊑lit-inv : ∀ {n m} → lit n ⊑ lit m → n ≡ m
lit⊑lit-inv ⊑-lit            = refl
lit⊑lit-inv (⊑-trans lt lt₁) = lit⊑lit-inv-mid lt lt₁
  where
    lit-mem : ∀ {n} {u : Value `ℕ} → lit n ≡ u → lit n ∈ u
    lit-mem {n} eq = Eq.subst (λ x → lit n ∈ x) eq refl
    lit⊑lit-inv-mid : ∀ {n m} {v : Value `ℕ}
                    → lit n ⊑ v → v ⊑ lit m → n ≡ m
    lit⊑lit-inv-mid {n} {m} lt lt₁
      with sub-inv-lit lt
    ... | u₂ , _ , u₂⊆v , eq
      with sub-inv-literal lt₁ (u₂⊆v (lit-mem eq))
    ... | u₃ , _ , u₃⊆litm , eq₂
      with u₃⊆litm (lit-mem eq₂)
    ... | refl = refl

preserve : ∀ {Γ} {γ : Env Γ} {A} {M : Γ ⊢ A} {N v}
  → γ ⊢ M ↓ v
  → M —→ N
    ----------
  → γ ⊢ N ↓ v
preserve (↓-↦-elim d d₁)  (ξ-·ₗ r)     = ↓-↦-elim (preserve d r) d₁
preserve (↓-↦-elim d d₁)  (ξ-·ᵣ r)     = ↓-↦-elim d (preserve d₁ r)
preserve (↓-↦-elim d d₁)  (β-· x)      = substitution (lambda-inversion d) d₁
preserve ↓-⊥-intro        r            = ↓-⊥-intro
preserve (↓-⊔-intro d d₁) r            = ↓-⊔-intro (preserve d r) (preserve d₁ r)
preserve (↓-sub d x)      r            = ↓-sub (preserve d r) x
preserve (↓-S d)          (ξ-S r)      = ↓-S (preserve d r)
preserve (↓-case-Z d d₁)  (ξ-case r)   = ↓-case-Z (preserve d r) d₁
preserve (↓-case-Z d d₁)  β-case-Z     = d₁
preserve (↓-case-Z d d₁)  (β-case-S x) = ⊥-elim (ℰS→𝒮ℰ d)
preserve (↓-case-S d d₁)  (ξ-case r)   = ↓-case-S (preserve d r) d₁
preserve (↓-case-S d d₁)  β-case-Z     = contradiction (lit⊑lit-inv (ℰ→𝒵 d)) λ ()
preserve (↓-case-S d d₁)  (β-case-S x) = substitution d₁ (suc-inversion d)
preserve (↓-μ d d₁)       (ξ-μ r)      = ↓-μ (preserve d r) (preserve d₁ (ξ-μ r))
preserve (↓-μ d d₁)       β-μ          = substitution (lambda-inversion d) d₁

lift-`⊑ : ∀ {Γ Δ A} {v : Value A} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Ren Γ Δ)
  → (δ ∘ ρ) `⊑ γ
    --------------------------------
  → ((δ `, v) ∘ lift ρ) `⊑ (γ `, v)
lift-`⊑ ρ lt Z = ⊑-refl
lift-`⊑ ρ lt (S x) = lt x

ren-reflect : ∀ {Γ Δ} {γ : Env Γ} {δ : Env Δ} {A} {M : Γ ⊢ A} {v}
  → {ρ : Ren Γ Δ}
  → (δ ∘ ρ) `⊑ γ
  → δ ⊢ ren ρ M ↓ v
    -----------------
  → γ ⊢ M ↓ v
ren-reflect {M = ` x} an d with var-inv d
... | lt = ↓-sub (↓-sub ↓-var (an x)) lt
ren-reflect {M = ƛ M} {ρ = ρ} an (↓-↦-intro d) =
  ↓-↦-intro (ren-reflect (lift-`⊑ ρ an) d)
ren-reflect {M = ƛ M} an ↓-⊥-intro = ↓-⊥-intro
ren-reflect {M = ƛ M} an (↓-⊔-intro d₁ d₂) =
  ↓-⊔-intro (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = ƛ M} an (↓-sub d x) = ↓-sub (ren-reflect an d) x
ren-reflect {M = M · N} an (↓-↦-elim d₁ d₂) =
  ↓-↦-elim (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = M · N} an ↓-⊥-intro = ↓-⊥-intro
ren-reflect {M = M · N} an (↓-⊔-intro d₁ d₂) =
  ↓-⊔-intro (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = M · N} an (↓-sub d x) = ↓-sub (ren-reflect an d) x
ren-reflect {M = `Z} an ↓-⊥-intro = ↓-⊥-intro
ren-reflect {M = `Z} an (↓-⊔-intro d₁ d₂) =
  ↓-⊔-intro (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = `Z} an (↓-sub d x) = ↓-sub (ren-reflect an d) x
ren-reflect {M = `Z} an ↓-Z = ↓-Z
ren-reflect {M = `S M} an ↓-⊥-intro = ↓-⊥-intro
ren-reflect {M = `S M} an (↓-⊔-intro d₁ d₂) =
  ↓-⊔-intro (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = `S M} an (↓-sub d x) = ↓-sub (ren-reflect an d) x
ren-reflect {M = `S M} an (↓-S d) = ↓-S (ren-reflect an d)
ren-reflect {M = case L M N} an ↓-⊥-intro = ↓-⊥-intro
ren-reflect {M = case L M N} an (↓-⊔-intro d₁ d₂) =
  ↓-⊔-intro (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = case L M N} an (↓-sub d x) = ↓-sub (ren-reflect an d) x
ren-reflect {M = case L M N} an (↓-case-Z d₁ d₂) =
  ↓-case-Z (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = case L M N} {ρ = ρ} an (↓-case-S d₁ d₂) =
  ↓-case-S (ren-reflect an d₁) (ren-reflect (lift-`⊑ ρ an) d₂)
ren-reflect {M = μ M} an ↓-⊥-intro = ↓-⊥-intro
ren-reflect {M = μ M} an (↓-⊔-intro d₁ d₂) =
  ↓-⊔-intro (ren-reflect an d₁) (ren-reflect an d₂)
ren-reflect {M = μ M} an (↓-sub d x) = ↓-sub (ren-reflect an d) x
ren-reflect {M = μ M} an (↓-μ d₁ d₂) =
  ↓-μ (ren-reflect an d₁) (ren-reflect an d₂)

ren-inc-reflect : ∀ {Γ A B} {γ : Env Γ} {M} {v : Value A} {v' : Value B}
  → (γ `, v') ⊢ ren S M ↓ v
    ----------------------------
  → γ ⊢ M ↓ v
ren-inc-reflect {γ = γ} d = ren-reflect (`⊑-refl {γ = γ}) d

_var≟_ : ∀ {Γ A B} → (x : Γ ∋ A) → (y : Γ ∋ B)
       → Dec (Σ[ eq ∈ A ≡ B ] Eq.subst (λ A → Γ ∋ A) eq x ≡ y)
Z var≟ Z = yes (refl , refl)
Z var≟ (S y) = no λ { (refl , ()) }
(S x) var≟ Z = no λ { (refl , ()) }
(S x) var≟ (S y) with x var≟ y
... | yes (refl , refl) = yes (refl , refl)
... | no ¬eq = no λ { (refl , p) → ¬eq (refl , S-injective (Eq.trans (subst-S refl x) p)) }
  where
  subst-S : ∀ {Γ A B C} (eq : A ≡ B) (x : Γ ∋ A)
    → Eq.subst (λ A → Γ ▷ C ∋ A) eq (S x) ≡ S (Eq.subst (λ A → Γ ∋ A) eq x)
  subst-S refl x = refl

  S-injective : ∀ {Γ A B} {x y : Γ ∋ A} → S {B = B} x ≡ S y → x ≡ y
  S-injective refl = refl

var≟-refl : ∀ {Γ A} (x : Γ ∋ A) → (x var≟ x) ≡ yes (refl , refl)
var≟-refl Z = refl
var≟-refl (S x) rewrite var≟-refl x = refl

const-env : ∀ {Γ A} → (x : Γ ∋ A) → Value A → Env Γ
const-env {A = A} x v {B} y with x var≟ y
... | yes (eq , _) = Eq.subst Value eq v
... | no _         = ⊥

same-const-env : ∀ {Γ A} {x : Γ ∋ A} {v} → (const-env x v) x ≡ v
same-const-env {x = x} rewrite var≟-refl x = refl

diff-const-env : ∀ {Γ A} {x y : Γ ∋ A} {v}
  → x ≢ y
    -------------------
  → const-env x v y ≡ ⊥
diff-const-env {x = x} {y} neq with x var≟ y
... | yes (refl , eq) = contradiction x λ z → neq eq
... | no _            = refl

sub-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {A} {x : Γ ∋ A} {v} {σ : Sub Γ Δ}
  → γ ⊢ σ x ↓ v
    -------------------------------------------
  → Σ[ δ ∈ Env Γ ] (γ `⊢ σ ↓ δ) × (δ ⊢ ` x ↓ v)
sub-reflect-var {Γ} {Δ} {γ} {A} {x} {v} {σ} xv
  rewrite Eq.sym (same-const-env {Γ} {x = x} {v}) =
    (const-env x v , const-env-ok , ↓-var)
  where
  const-env-ok : γ `⊢ σ ↓ const-env x v
  const-env-ok y with x var≟ y
  ... | yes (refl , x≡y) rewrite Eq.sym x≡y | same-const-env {Γ} {x = x} {v} = xv
  ... | no x≢y = ↓-⊥-intro

sub-⊥ : ∀{Γ Δ} {γ : Env Δ} {σ : Sub Γ Δ}
    -----------------
  → γ `⊢ σ ↓ `⊥
sub-⊥ x = ↓-⊥-intro

sub-⊔ : ∀ {Γ Δ} {γ : Env Δ} {γ₁ γ₂ : Env Γ} {σ : Sub Γ Δ}
      → γ `⊢ σ ↓ γ₁
      → γ `⊢ σ ↓ γ₂
        -------------------------
      → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
sub-⊔ γ₁-ok γ₂-ok x = ↓-⊔-intro (γ₁-ok x) (γ₂-ok x)

lambda-inj : ∀ {Γ A B} {M N : Γ ▷ A ⊢ B}
  → (ƛ M) ≡ (ƛ N)
    --------------
  → M ≡ N
lambda-inj refl = refl

suc-inj : ∀ {Γ} {M N : Γ ⊢ `ℕ}
  → (`S M) ≡ (`S N)
    --------------
  → M ≡ N
suc-inj refl = refl 

case-inj : ∀ {Γ A} {L L' M M'} {N N' : Γ ▷ `ℕ ⊢ A}
  → (case L M N) ≡ (case L' M' N')
    --------------
  → L ≡ L' × M ≡ M' × N ≡ N'
case-inj refl = refl , refl , refl 

fix-inj  : ∀ {Γ A} {M N : Γ ⊢ A ⇒ A}
  → (μ M) ≡ (μ N)
    --------------
  → M ≡ N
fix-inj refl = refl

-- i'm not sure what happens here
-- this should be straightforward Eq.subst with init-last
-- but it seems that there is a weird unification/elaboration
-- problem related to implicit parameters (or something similar)
postulate
 split : ∀ {Γ A B} {δ : Env (Γ ▷ A)} {M : Γ ▷ A ⊢ B} {v}
  → δ ⊢ M ↓ v
    --------------------------
  → (init δ `, last δ) ⊢ M ↓ v
-- split {δ = δ} {M} {v} δMv = Eq.subst (λ γ → γ ⊢ M ↓ v) (init-last δ) δMv

sub-reflect : ∀ {Γ Δ} {δ : Env Δ} {A} {M : Γ ⊢ A} {v} {L : Δ ⊢ A} {σ : Sub Γ Δ}
  → δ ⊢ L ↓ v
  → sub σ M ≡ L
    ------------------------------------------
  → Σ[ γ ∈ Env Γ ] (δ `⊢ σ ↓ γ) × (γ ⊢ M ↓ v)

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} ↓-var eq
    with M 
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) ↓-var) 
sub-reflect {δ = δ} {M = M} {σ = σ} (↓-var {x = _}) () | ƛ M'
sub-reflect {δ = δ} {M = M} {σ = σ} (↓-var {x = _}) () | M' · M''
sub-reflect {δ = δ} {M = M} {σ = σ} (↓-var {x = _}) () | `Z
sub-reflect {δ = δ} {M = M} {σ = σ} (↓-var {x = _}) () | `S M'
sub-reflect {δ = δ} {M = M} {σ = σ} (↓-var {x = _}) () | case M' M'' M'''
sub-reflect {δ = δ} {M = M} {σ = σ} (↓-var {x = _}) () | μ M'

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} (↓-↦-elim d₁ d₂) eq
    with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) (↓-↦-elim d₁ d₂))
... | M₁ · M₂
    with refl ← eq
    with sub-reflect {M = M₁} d₁ refl | sub-reflect {M = M₂} d₂ refl
... | (δ₁ , sd1 , m1) | (δ₂ , sd2 , m2)
    = (δ₁ `⊔ δ₂) , sub-⊔ sd1 sd2
    , ↓-↦-elim (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂)) (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂))

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} (↓-↦-intro d) eq
  with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) (↓-↦-intro d))
... | ƛ M'
    with sub-reflect {M = M'} {σ = lifts σ} d (lambda-inj eq)
... | (δ' , sd' , m')
    = init δ' , (λ x → ren-inc-reflect (sd' (S x)))
    , ↓-↦-intro (up-env (split m') (var-inv (sd' Z)))

sub-reflect {M = M} {σ = σ} ↓-⊥-intro eq = `⊥ , sub-⊥ {σ = σ} , ↓-⊥-intro

sub-reflect {M = M} {σ = σ} (↓-⊔-intro d₁ d₂) eq
    with sub-reflect {M = M} {σ = σ} d₁ eq | sub-reflect {M = M} {σ = σ} d₂ eq
... | (δ₁ , sd1 , m1) | (δ₂ , sd2 , m2)
    = (δ₁ `⊔ δ₂ , sub-⊔ sd1 sd2
    , ↓-⊔-intro (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂)) (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂)))

sub-reflect {M = M} {σ = σ} (↓-sub d x) eq
    with sub-reflect {M = M} {σ = σ} d eq
... | (δ' , sd' , m') = δ' , sd' , ↓-sub m' x

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} ↓-Z eq
    with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) ↓-Z)
... | `Z =  `⊥ , sub-⊥ {σ = σ} , ↓-Z

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} (↓-S d) eq
    with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) (↓-S d))
... | `S M'
    with sub-reflect {M = M'} {σ = σ} d (suc-inj eq)
... | (δ' , sd' , m') = δ' , sd' , ↓-S m'

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} (↓-case-Z d₁ d₂) eq
    with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) (↓-case-Z d₁ d₂))
... | case M₁ M₂ M₃
    with (eq1 , eq2 , eq3) ← case-inj eq
    with (δ₁ , sd1 , m1) ← sub-reflect {M = M₁} {σ = σ} d₁ eq1
    with (δ₂ , sd2 , m2) ← sub-reflect {M = M₂} {σ = σ} d₂ eq2 
    = (δ₁ `⊔ δ₂) , sub-⊔ sd1 sd2
    , ↓-case-Z (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂)) (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂))

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} (↓-case-S d₁ d₂) eq
    with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) (↓-case-S d₁ d₂))
... | case M₁ M₂ M₃
    with (eq1 , eq2 , eq3) ← case-inj eq
    with (δ₁ , sd1 , m1) ← sub-reflect {M = M₁} {σ = σ} d₁ eq1
    with (δ₂ , sd2 , m2) ← sub-reflect {M = M₃} {σ = lifts σ} d₂ eq3
    = (δ₁ `⊔ init δ₂) , sub-⊔ sd1 (λ x → ren-inc-reflect (sd2 (S x)))
    , ↓-case-S (⊑-env m1 (⊑-env-conj-R1 δ₁ (init δ₂)))
               (⊑-env (split m2) λ { Z → var-inv (sd2 Z) ; (S x) → ⊑-env-conj-R2 δ₁ (init δ₂) x })

sub-reflect {δ = δ} {M = M} {v = v} {σ = σ} (↓-μ d₁ d₂) eq
    with M
... | ` x = sub-reflect-var (Eq.subst (λ z → δ ⊢ z ↓ v) (Eq.sym eq) (↓-μ d₁ d₂))
... | μ M' with refl ← eq
    with (δ₁ , sd1 , m1) ← sub-reflect {M = M'} {σ = σ} d₁ refl
    with (δ₂ , sd2 , m2) ← sub-reflect {M = μ M'} {σ = σ} d₂ refl
    = (δ₁ `⊔ δ₂) , sub-⊔ sd1 sd2
    , (↓-μ (⊑-env m1 (⊑-env-conj-R1 δ₁ δ₂)) (⊑-env m2 (⊑-env-conj-R2 δ₁ δ₂)))

sub-zero-reflect : ∀ {Δ} {δ : Env Δ} {A} {γ : Env (Δ ▷ A)} {M : Δ ⊢ A}
  → δ `⊢ sub-zero M ↓ γ
    --------------------------------------------
  → Σ[ w ∈ Value _ ] γ `⊑ (δ `, w) × δ ⊢ M ↓ w
sub-zero-reflect {δ = δ} {γ = γ} δσγ = (last γ , lemma , δσγ Z)
  where
  lemma : γ `⊑ (δ `, last γ)
  lemma Z     =  ⊑-refl
  lemma (S x) = var-inv (δσγ (S x))

substitution-reflect : ∀ {Δ} {δ : Env Δ} {A B} {N : Δ ▷ A ⊢ B} {M : Δ ⊢ A} {v}
  → δ ⊢ N [ M ] ↓ v
    ------------------------------------------------
  → Σ[ w ∈ Value _ ] δ ⊢ M ↓ w  ×  (δ `, w) ⊢ N ↓ v
substitution-reflect d
  with (γ , δσγ , γNv) ← sub-reflect d refl
  with (w , ineq , δMw) ← sub-zero-reflect δσγ
  = (w , δMw , ⊑-env γNv ineq)

reflect-app : ∀ {Γ} {γ : Env Γ} {A B} {N : Γ ▷ A ⊢ B} {M v}
    → γ ⊢ (N [ M ]) ↓ v
    → γ ⊢ (ƛ N) · M ↓ v
reflect-app d
  with (v₂' , d₁' , d₂') ← substitution-reflect d
  = ↓-↦-elim (↓-↦-intro d₂') d₁'

val-num : ∀ {Γ} {L : Γ ⊢ `ℕ} → Val L → ℕ
val-num V-Z       = zero
val-num (V-S val) = suc (val-num val)
 
val-num-↓ : ∀ {Γ} {γ : Env Γ} {L : Γ ⊢ `ℕ}
  → (val : Val L) → γ ⊢ L ↓ lit (val-num val)
val-num-↓ V-Z       = ↓-Z
val-num-↓ (V-S val) = ↓-S (val-num-↓ val)
 
𝒮-inv : ∀ {Γ} {γ : Env Γ} {M : Γ ⊢ `ℕ} {n w}
  → (∀ {w'} → γ ⊢ M ↓ w' → w' ⊑ lit n)
  → 𝒮 (ℰ M) γ w
  → w ⊑ lit (suc n)
𝒮-inv {w = ⊥}           ih s         = ⊑-bot
𝒮-inv {w = lit zero}    ih s         = ⊥-elim s
𝒮-inv {w = lit (suc x)} ih s         with refl ← lit⊑lit-inv (ih s) = ⊑-refl
𝒮-inv {w = w₁ ⊔ w₂}     ih (s₁ , s₂) = ⊑-conj-L (𝒮-inv ih s₁) (𝒮-inv ih s₂)
 
val-num-inv : ∀ {Γ} {γ : Env Γ} {L : Γ ⊢ `ℕ} {w}
  → (val : Val L) → γ ⊢ L ↓ w → w ⊑ lit (val-num val)
val-num-inv V-Z       d = ℰ→𝒵 d
val-num-inv (V-S val) d = 𝒮-inv (val-num-inv val) (ℰS→𝒮ℰ d)

reflect-case : ∀ {Γ} {γ : Env Γ} {A} {N : Γ ▷ `ℕ ⊢ A} {L M v}
    → Val L
    → γ ⊢ (N [ L ]) ↓ v
    → γ ⊢ case (`S L) M N ↓ v
reflect-case {N = N} {L} {M} val d
  with (v₂' , d₁' , d₂') ← substitution-reflect {N = N} {M = L} d
  = ↓-case-S (↓-S (val-num-↓ val)) (up-env d₂' (val-num-inv val d₁'))

reflect-fix : ∀ {Γ} {γ : Env Γ} {A} {M : Γ ▷ A ⊢ A} {v}
    → γ ⊢ (M [ μ ƛ M ]) ↓ v
    → γ ⊢ (μ ƛ M) ↓ v
reflect-fix d
  with (v' , d₁' , d₂') ← substitution-reflect d
  = ↓-μ (↓-↦-intro d₂') d₁'

reflect : ∀ {Γ} {γ : Env Γ} {A} {M M' N : Γ ⊢ A} {v}
  → γ ⊢ N ↓ v  →  M —→ M'  →   M' ≡ N
    ---------------------------------
  → γ ⊢ M ↓ v
reflect {γ = γ} (↓-var {x = x}) (β-· v) eq
  = reflect-app (Eq.subst (λ M → γ ⊢ M ↓ γ x) (Eq.sym eq) ↓-var)
reflect ↓-var β-case-Z refl = ↓-case-Z ↓-Z ↓-var
reflect {γ = γ} (↓-var {x = x}) (β-case-S {L = L} {N = N} v) eq
  = reflect-case v (Eq.subst (λ M → γ ⊢ M ↓ γ x) (Eq.sym eq) ↓-var)
reflect {γ = γ} (↓-var {x = x}) (β-μ {M = M}) eq
  = reflect-fix (Eq.subst (λ M → γ ⊢ M ↓ γ x) (Eq.sym eq) ↓-var)

reflect (↓-↦-elim d₁ d₂) (ξ-·ₗ r) refl = ↓-↦-elim (reflect d₁ r refl) d₂
reflect (↓-↦-elim d₁ d₂) (ξ-·ᵣ r) refl = ↓-↦-elim d₁ (reflect d₂ r refl)
reflect (↓-↦-elim d₁ d₂) (β-· v) eq
  = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-↦-elim d₁ d₂))
reflect (↓-↦-elim d₁ d₂) β-case-Z refl = ↓-case-Z ↓-Z (↓-↦-elim d₁ d₂)
reflect (↓-↦-elim d₁ d₂) (β-case-S v) eq
  = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-↦-elim d₁ d₂))
reflect (↓-↦-elim d₁ d₂) β-μ eq
  = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-↦-elim d₁ d₂))

reflect (↓-↦-intro d) (β-· x) eq
  = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-↦-intro d))
reflect (↓-↦-intro d) β-case-Z refl = ↓-case-Z ↓-Z (↓-↦-intro d)
reflect (↓-↦-intro d) (β-case-S v) eq
  = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-↦-intro d))
reflect (↓-↦-intro d) β-μ eq
  = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-↦-intro d))

reflect ↓-⊥-intro r eq = ↓-⊥-intro

reflect (↓-⊔-intro d₁ d₂) r eq = ↓-⊔-intro (reflect d₁ r eq) (reflect d₂ r eq)

reflect (↓-sub d lt) r eq = ↓-sub (reflect d r eq) lt

reflect ↓-Z (β-· x) eq = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) ↓-Z)
reflect ↓-Z β-case-Z refl = ↓-case-Z ↓-Z ↓-Z
reflect ↓-Z (β-case-S v) eq
  = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) ↓-Z)
reflect ↓-Z β-μ eq = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) ↓-Z)

reflect (↓-S d) (β-· x) eq
  = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-S d))
reflect (↓-S d) (ξ-S r) refl = ↓-S (reflect d r refl)
reflect (↓-S d) β-case-Z refl = ↓-case-Z ↓-Z (↓-S d)
reflect (↓-S d) (β-case-S v) eq
 = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-S d))
reflect (↓-S d) β-μ eq
  = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-S d))

reflect (↓-case-Z d₁ d₂) (β-· x) eq
  = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-case-Z d₁ d₂))
reflect (↓-case-Z d₁ d₂) (ξ-case r) refl = ↓-case-Z (reflect d₁ r refl) d₂
reflect (↓-case-Z d₁ d₂) β-case-Z refl = ↓-case-Z ↓-Z (↓-case-Z d₁ d₂)
reflect (↓-case-Z d₁ d₂) (β-case-S v) eq
  = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-case-Z d₁ d₂))
reflect (↓-case-Z d₁ d₂) β-μ eq
  = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-case-Z d₁ d₂))

reflect (↓-case-S d₁ d₂) (β-· x) eq
  = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-case-S d₁ d₂))
reflect (↓-case-S d₁ d₂) (ξ-case r) refl = ↓-case-S (reflect d₁ r refl) d₂
reflect (↓-case-S d₁ d₂) β-case-Z refl = ↓-case-Z ↓-Z (↓-case-S d₁ d₂)
reflect (↓-case-S d₁ d₂) (β-case-S v) eq
  = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-case-S d₁ d₂))
reflect (↓-case-S d₁ d₂) β-μ eq
  = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-case-S d₁ d₂))

reflect (↓-μ d₁ d₂) (β-· x) eq
  = reflect-app (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-μ d₁ d₂))
reflect (↓-μ d₁ d₂) β-case-Z refl = ↓-case-Z ↓-Z (↓-μ d₁ d₂)
reflect (↓-μ d₁ d₂) (β-case-S v) eq
  = reflect-case v (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-μ d₁ d₂))
reflect (↓-μ d₁ d₂) (ξ-μ r) refl = ↓-μ (reflect d₁ r refl) (reflect d₂ (ξ-μ r) refl)
reflect (↓-μ d₁ d₂) β-μ eq
  = reflect-fix (Eq.subst (λ M → _ ⊢ M ↓ _) (Eq.sym eq) (↓-μ d₁ d₂))

reduce-equal : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal r γ v = ((λ m → preserve m r) , (λ n → reflect n r refl))
