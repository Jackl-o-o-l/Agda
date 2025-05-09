module test where

open import lib
open import source
open import target
open import compiler

-- term0 : nothing
term0 : · ⊢ comm
term0 = Skip
result0 = compile-closed term0

-- term1 : x := 2
term1 : · ⊢ comm
term1 = 
    NewVar 
        (Assign 
            (Sub (Var Zero) var-≤:-acc) 
            (Lit (pos 2)))
result1 = compile-closed term1

-- term2 : x := (λ a. a) -4
term2 : · ⊢ comm
term2 = 
    NewVar 
        (Assign 
            (Sub (Var Zero) var-≤:-acc) 
            (App 
                (Lambda (Var Zero)) 
                (Lit (negsuc 3))))
result2 = compile-closed term2

-- term3 : x := (λ a. (λ b. a + b) 2) 3
term3 : · ⊢ comm
term3 = 
    NewVar 
        (Assign 
            (Sub (Var Zero) var-≤:-acc) 
            (App 
                (Lambda 
                    (App 
                        (Lambda 
                            (Plus 
                                (Var (Suc Zero))
                                (Var Zero)))
                        (Lit (pos 2))))
                (Lit (pos 3))))
result3 = compile-closed term3

-- term3' : x := 3 + 2
term3' : · ⊢ comm
term3' = 
    NewVar 
        (Assign 
            (Sub (Var Zero) var-≤:-acc) 
            (Plus 
                (Lit (pos 3)) 
                (Lit (pos 2))))
result3' = compile-closed term3'


-- term4 : x := -3; y := (λ a. x) 2
term4 : · ⊢ comm
term4 = 
    NewVar 
        (Seq 
            (Assign 
                (Sub (Var Zero) var-≤:-acc) 
                (Lit (negsuc 2)))
            (NewVar 
                (Assign 
                    (Sub (Var (Suc Zero)) var-≤:-acc)
                    (App 
                        (Lambda (Sub (Var (Suc (Suc Zero))) var-≤:-exp))
                        (Lit (pos 2))))))
result4 = compile-closed term4

-- term5 : x := 2; x := x + 1
term5 : · ⊢ comm
term5 = 
    NewVar 
        (Seq 
            (Assign 
                (Sub (Var Zero) var-≤:-acc) 
                (Lit (pos 2))) 
            (Assign 
                (Sub (Var Zero) var-≤:-acc)
                (Plus 
                    (Sub (Var Zero) var-≤:-exp) 
                    (Lit (pos 1)))))
result5 = compile-closed term5

-- term5' : x := 2; skip; x := x + 1
term5' : · ⊢ comm
term5' = 
    NewVar 
        (Seq 
            (Seq 
                (Assign 
                    (Sub (Var Zero) var-≤:-acc) 
                    (Lit (pos 2))) 
                Skip)
            (Assign 
                (Sub (Var Zero) var-≤:-acc)
                (Plus 
                    (Sub (Var Zero) var-≤:-exp) 
                    (Lit (pos 1)))))
result5' = compile-closed term5'

-- term6 : x := 2; x := -x + 1
term6 : · ⊢ comm
term6 = 
    NewVar 
        (Seq 
            (Assign 
                (Sub (Var Zero) var-≤:-acc) 
                (Lit (pos 2)))
            (Assign 
                ((Sub (Var Zero) var-≤:-acc)) 
                (Plus 
                    (Neg (Sub (Var Zero) var-≤:-exp)) 
                    (Lit (pos 1)))))
result6 = compile-closed term6

-- term7 : x := (λ a. -a + 1) 2
term7 : · ⊢ comm
term7 = 
    NewVar 
        (Assign 
            (Sub (Var Zero) var-≤:-acc) 
            (App 
                (Lambda 
                    (Plus 
                        (Neg (Var Zero))
                        (Lit (pos 1)))) 
                (Lit (pos 2))))
result7 = compile-closed term7
