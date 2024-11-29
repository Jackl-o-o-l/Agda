data Type : Set where
    comm : Type
    intexp : Type
    intacc : Type
    intvar : Type
    ℕ : Type
    ℤ : Type
    _⇒_ : Type → Type → Type


infix 4 _⊢_
infix 4 _∈_

infixl 5 _,_
infixr 7 _⇒_ 

data Context : Set where
    · : Context
    _,_ : Context → Type → Context

data _∈_ : Type → Context → Set where
    Z : ∀{Γ A} → A ∈ Γ , A
    S : ∀{Γ A B} → B ∈ Γ → B ∈ Γ , A

data _⊢_ : Context → Type → Set where
    Var : ∀{Γ A} → A ∈ Γ → Γ ⊢ A

    -- lambda function and application
    Lambda : ∀{Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
    App : ∀{Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

    -- constant
    Zero : ∀ {Γ} → Γ ⊢ ℕ
    Suc : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℕ
    Pos : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℤ
    Negsuc : ∀ {Γ} → Γ ⊢ ℕ → Γ ⊢ ℤ

-- QUESTION: should i add "_" after things like S, suc, pos, etc.?

data Value : ∀{Γ A} → Γ ⊢ A → Set where
    V-Zero : ∀{Γ} → Value (Zero {Γ})
    V-Suc : ∀{Γ} {V : Γ ⊢ ℕ} → Value V → Value (Suc V)
    V-Pos : ∀{Γ} {V : Γ ⊢ ℕ} → Value V → Value (Pos V) 
    V-Negsuc : ∀{Γ} {V : Γ ⊢ ℕ} → Value V → Value (Pos V) 

    V-Lambda : ∀{Γ A B} {F : Γ , A ⊢ B} → Value (Lambda F)

infix 2 _⟶_ 

data _⟶_ : ∀{Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
    Suc-cong : ∀{Γ} {N N′ : Γ ⊢ ℕ} → N ⟶ N′ → Suc N ⟶ Suc N′
    Pos-cong : ∀{Γ} {N N′ : Γ ⊢ ℕ} → N ⟶ N′ → Pos N ⟶ Pos N′
    Negsuc-cong : ∀{Γ} {N N′ : Γ ⊢ ℕ} → N ⟶ N′ → Negsuc N ⟶ Negsuc N′
    
    App-cong₁ : ∀{Γ A B} {F F′ : Γ ⊢ A ⇒ B} {E : Γ ⊢ A} → F ⟶ F′ → App F E ⟶ App F′ E
    App-cong₂ : ∀{Γ A B} {V : Γ ⊢ A ⇒ B} {E E′ : Γ ⊢ A} → Value V → E ⟶ E′ → App V E ⟶ App V E′

infix 1 _≤:_

data _≤:_ : Type → Type → Set where
    ≤:-refl : ∀{T} → T ≤: T
    ≤:-trans : ∀{T T′ T″} → T ≤: T′ → T′ ≤: T″ → T ≤: T″
    ≤:-fn : ∀{T₁ T₁′ T₂ T₂′} → T₁′ ≤: T₁ → T₂ ≤: T₂′ → T₁ ⇒ T₂ ≤: T₁′ ⇒ T₂′

    var-≤:-exp : intvar ≤: intexp
    var-≤:-acc : intvar ≤: intacc