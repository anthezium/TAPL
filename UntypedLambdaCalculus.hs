{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module UntypedLambdaCalculus where

import Data.Set

data Term v = Var v                 -- named variables,      like x
            | Lam v        (Term v) -- lambda terms,         like (\x -> (z (y x)))
            | App (Term v) (Term v) -- function application, like (y x)

deriving instance Show v => Show (Term v)
deriving instance Eq v => Eq (Term v)
deriving instance Functor Term

subst :: Eq v => v -> v -> (v -> v)
subst v v' x = if x == v then v' else x

applySubst :: Eq v => (v -> v) -> Term v -> Term v
applySubst s (Var x)   = Var $ s x
applySubst s (App l r) = App (applySubst s l) (applySubst s r)
applySubst s (Lam x t) = Lam x $ applySubst s t

uniqueify :: Term String -> Term String
uniqueify t = let (t', _, _) = helper t 0 empty
              in t'
  where helper (Var x)   i vs = (Var x, i, insert x vs)
        helper (App l r) i vs = let (l', i',  vs')  = helper l i  vs
                                    (r', i'', vs'') = helper r i' vs'
                                in (App l' r', i'', vs'')
        helper (Lam x t) i vs = let (x', i',  vs')  = freshen x i vs
                                    (t', i'', vs'') = helper (applySubst (subst x x') t) i' vs'
                                in (Lam x' t', i'', vs'')
        freshen x i vs = if member x vs
                            then freshen (x ++ "$" ++ show i) (i + 1) vs
                            else (x, i, insert x vs)

eval :: (Eq v) => (v -> Term v) -> Term v -> Term v
eval env (Var x)   = env x
eval env (App l r) = 
  let r' = eval env r -- evaluate argument first => call-by-value.
  in case eval env l of 
          (Lam x t) -> eval (\ y -> if y == x then r' else env y) t -- substitute the evaluated argument for its name
                                                                    -- inside the body.
          l'        -> App l' r'
eval env (Lam x t) = Lam x $ eval (\ y -> if y == x then Var x else env y) t -- don't use previous bindings for x
                                                                             -- inside the body.

evalTop :: Term String -> Term String
evalTop = eval emptyEnv . uniqueify
  where emptyEnv x = Var x

toDeBruijn :: Eq v => Term v -> Term Integer
toDeBruijn t = helper t 0
  where helper (Var x)   i = Var x
        helper (Lam x t) i = 

        dbSubst s (Var x)   = Var $ s x
        dbSubst s (App l r) = App (dbSubst s l) (dbSubst s r)
        dbSubst s (Lam x t) = let s' = \ y -> if y == x then "0" else show . (+ 1) . read . s
                              in Lam "0" $ dbSubst s' t

lambdaId   = Lam "x" (Var "x")
churchZero = Lam "f" lambdaId
churchSucc = Lam "c" (Lam "f" (Lam "x" (App (Var "f") (App (App (Var "c") (Var "f")) (Var "x")))))
churchOne  = App churchSucc churchZero
churchTwo  = App churchSucc churchOne

capture = Lam "x" (Lam "x" (Var "x"))
capturex = (App capture (Var "y"))

tru = Lam "t" (Lam "f" (Var "t"))  -- same as const
fls = Lam "t" (Lam "f" (Var "f"))  -- same as churchZero

test = Lam "l" $ Lam "m" $ Lam "n" $ App (App (Var "l") (Var "m")) (Var "n")

and = Lam "b" $ Lam "c" $ App (App (Var "b") (Var "c")) fls

or = Lam "b" $ Lam "c" $ App (App (Var "b") tru) (Var "c")
