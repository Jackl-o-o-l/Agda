data Type : Set where
    comm : Type
    intexp : Type
    intacc : Type
    intvar : Type
    ℕ : Type
    ℤ : Type
    _⇒_ : Type → Type → Type

infix 30 _,_
infix 30 _⇒_ 

data Context : Set where
    · : Context
    _,_ : Context → Type → Context

data _∈_ : Type → Context → Set where
    Z : ∀{Γ A} → A ∈ Γ , A
    S : ∀{Γ A B} → B ∈ Γ → B ∈ Γ , A

data _⊢_ : Context → Type → Set where
    Var : ∀{Γ A} → A ∈ Γ → Γ ⊢ A

    Lambda : ∀{Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
    App : ∀{Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

    zero : ∀ {Γ} → Γ ⊢ ℕ
    suc : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℕ
    pos : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℤ
    negsuc : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℤ

-- QUESTION: should i add "_" after things like S, suc, pos, etc.?

data Value : ∀{Γ A} → Γ ⊢ A → Set where
    V-zero : ∀{Γ} → Value (zero {Γ})
    V-suc : ∀{Γ} {V : Γ ⊢ ℕ} → Value V → Value (suc V)
    V-pos : ∀{Γ} {V : Γ ⊢ ℕ} → Value V → Value (pos V) 
    V-negsuc : ∀{Γ} {V : Γ ⊢ ℕ} → Value V → Value (pos V) 

    V-Lambda : ∀{Γ A B} {P : Γ , A ⊢ B} → Value (Lambda P)

-- infix 2 _⟶_ 

-- data _⟶_ : ∀{Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
--     fun