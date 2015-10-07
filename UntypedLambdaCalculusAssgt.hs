{-# LANGUAGE FlexibleContexts, StandaloneDeriving #-}
module UntypedLambdaCalculus where

data Term v = Var v                 -- named variables,      like x
            | Lam v        (Term v) -- lambda terms,         like (\x -> (z (y x)))
            | App (Term v) (Term v) -- function application, like (y x)

deriving instance Show v => Show (Term v)
deriving instance Eq v => Eq (Term v)

eval :: (Eq v) => (v -> Term v) -> Term v -> Term v
eval env (Var x)   = undefined
eval env (App l r) = undefined
eval env (Lam x t) = undefined

evalTop :: (Eq v) => Term v -> Term v
evalTop = undefined

lambdaId   = Lam 'x' (Var 'x')
churchZero = Lam 'f' lambdaId
churchSucc = Lam 'c' (Lam 'f' (Lam 'x' (App (Var 'f') (App (App (Var 'c') (Var 'f')) (Var 'x')))))
churchOne  = App churchSucc churchZero
churchTwo  = App churchSucc churchOne

capture = Lam 'x' (Lam 'x' (Var 'x'))
capturex = (App capture (Var 'y'))
