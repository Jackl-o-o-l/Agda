module compiler where

open import source
open import target

Env : Context → SD → Set
Env Γ sd = ∀ {A} → A ∈ Γ → L sd