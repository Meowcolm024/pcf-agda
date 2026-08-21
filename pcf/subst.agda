module pcf.subst where

open import pcf.base

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (id; _∘_)

⟪_⟫ : ∀ {Γ Δ A} → Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ = sub σ

↑ : ∀ {Γ A} → Sub Γ (Γ ▷ A)
↑ x = ` (S x)

infixr 5 _⨟_

_⨟_ : ∀ {Γ Δ Σ} → Sub Γ Δ → Sub Δ Σ → Sub Γ Σ
σ ⨟ τ = ⟪ τ ⟫ ∘ σ

subren : ∀ {Γ Δ} → Ren Γ Δ → Sub Γ Δ
subren ρ = ids ∘ ρ

postulate
  ren-sub-ren : ∀ {Γ Δ} {A} {ρ : Ren Γ Δ} {M : Γ ⊢ A}
              → ren ρ M ≡ ⟪ subren ρ ⟫ M
  sub-id : ∀ {Γ} {A} {M : Γ ⊢ A} → ⟪ ids ⟫ M ≡ M
  ren-id : ∀ {Γ} {A} {M : Γ ⊢ A} → ren id M ≡ M
