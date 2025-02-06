module compiler where

open import source
open import target

Env : Context → SD → Set
Env Γ sd = ∀ {A} → A ∈ Γ → L sd

extend-env : ∀ {Γ A sd} → Env Γ sd → L sd → Env (Γ , A) (sd +ₛ 1)