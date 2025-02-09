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
⟦ comm ⟧ty s = ∀{s'} → (s ≤ₛ s') → I s' → I s'
⟦ intexp ⟧ty s = ∀{s'} → (s ≤ₛ s') → (R s' → I s') → I s'
⟦ intacc ⟧ty s = ∀{s'} → (s ≤ₛ s') → I s' → (R s' → I s')
⟦ intvar ⟧ty s = ⟦ intexp ⟧ty s × ⟦ intacc ⟧ty s
⟦ source.ℕ ⟧ty s = R s
⟦ source.ℤ ⟧ty s = R s
⟦ θ₁ ⇒ θ₂ ⟧ty s = ∀{s'} → (s ≤ₛ s') → ⟦ θ₁ ⟧ty s' → ⟦ θ₂ ⟧ty s'

-- Unit type for empty context
data ∅ : Set where
    unit : ∅

-- Context Interpretation
⟦_⟧ctx : Context → SD → Set
⟦ · ⟧ctx _ = ∅
⟦ Γ , A ⟧ctx s = ⟦ Γ ⟧ctx s × ⟦ A ⟧ty s