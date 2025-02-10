module compiler where

open import source
open import target

infixr 2 _×_

-- Product and projection function
data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

π₁ : ∀ {A B} → A × B → A
π₁ (a , _) = a

π₂ : ∀ {A B} → A × B → B
π₂ (_ , b) = b

--  Type Interpretation
⟦_⟧ty : Type → SD → Set
⟦ comm ⟧ty sd = ∀{sd'} → (sd ≤ₛ sd') → I sd' → I sd'
⟦ intexp ⟧ty sd = ∀{sd'} → (sd ≤ₛ sd') → (R sd' → I sd') → I sd'
⟦ intacc ⟧ty sd = ∀{sd'} → (sd ≤ₛ sd') → I sd' → (R sd' → I sd')
⟦ intvar ⟧ty sd = ⟦ intexp ⟧ty sd × ⟦ intacc ⟧ty sd
⟦ source.ℕ ⟧ty sd = R sd
⟦ source.ℤ ⟧ty sd = R sd
⟦ θ₁ ⇒ θ₂ ⟧ty sd = ∀{sd'} → (sd ≤ₛ sd') → ⟦ θ₁ ⟧ty sd' → ⟦ θ₂ ⟧ty sd'

-- Unit type for empty context
data ∅ : Set where
    unit : ∅

-- Context Interpretation
⟦_⟧ctx : Context → SD → Set
⟦ · ⟧ctx _ = ∅
⟦ Γ , A ⟧ctx sd = ⟦ Γ ⟧ctx sd × ⟦ A ⟧ty sd

-- ⟦_⊢_⟧ : ∀ {Γ A sd} → Γ ⊢ A → ⟦ Γ ⟧ctx sd → ⟦ A ⟧ty sd