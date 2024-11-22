data Type : Set where
    comm : Type
    intexp : Type
    intacc : Type
    intvar : Type
    _⇒_ : Type → Type → Type

infix 30 _,_

data Context : Set where
    · : Context
    _,_ : Context → Type → Context

data _∈_ : Type → Context → Set where
    Z : ∀{Γ A} → A ∈ Γ , A
    S : ∀{Γ A B} → B ∈ Γ → B ∈ Γ , A

data _⊢_ : Context → Type → Set where
    Var : ∀{Γ A} → A ∈ Γ → Γ ⊢ A
    