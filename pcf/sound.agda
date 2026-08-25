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

subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {A} {x : Γ ∋ A} {v} {σ : Sub Γ Δ}
  → γ ⊢ σ x ↓ v
    -------------------------------------------
  → Σ[ δ ∈ Env Γ ] (γ `⊢ σ ↓ δ) × (δ ⊢ ` x ↓ v)
subst-reflect-var {Γ} {Δ} {γ} {A} {x} {v} {σ} xv
  rewrite Eq.sym (same-const-env {Γ} {x = x} {v}) =
    (const-env x v , const-env-ok , ↓-var)
  where
  const-env-ok : γ `⊢ σ ↓ const-env x v
  const-env-ok y with x var≟ y
  ... | yes (refl , x≡y) rewrite Eq.sym x≡y | same-const-env {Γ} {x = x} {v} = xv
  ... | no x≢y = ↓-⊥-intro

subst-⊥ : ∀{Γ Δ} {γ : Env Δ} {σ : Sub Γ Δ}
    -----------------
  → γ `⊢ σ ↓ `⊥
subst-⊥ x = ↓-⊥-intro

subst-⊔ : ∀ {Γ Δ} {γ : Env Δ} {γ₁ γ₂ : Env Γ} {σ : Sub Γ Δ}
        → γ `⊢ σ ↓ γ₁
        → γ `⊢ σ ↓ γ₂
          -------------------------
        → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
subst-⊔ γ₁-ok γ₂-ok x = ↓-⊔-intro (γ₁-ok x) (γ₂-ok x)

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
postulate
 split : ∀ {Γ A B} {δ : Env (Γ ▷ A)} {M : Γ ▷ A ⊢ B} {v}
  → δ ⊢ M ↓ v
    --------------------------
  → (init δ `, last δ) ⊢ M ↓ v
-- split {δ = δ} {M} {v} δMv = Eq.subst (λ γ → γ ⊢ M ↓ v) (init-last δ) δMv
