{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module UntypedLambdaCalculus where

import qualified Data.Map as M
import Data.Set
import Debug.Trace

data Term v = Var v                 -- named variables,      like x
            | Lam v        (Term v) -- lambda terms,         like (\x -> (z (y x)))
            | App (Term v) (Term v) -- function application, like (y x)

deriving instance Show v => Show (Term v)
deriving instance Eq v => Eq (Term v)
deriving instance Functor Term

subst :: Eq v => v -> v -> (v -> v)
subst v v' x = if x == v then v' else x

applyNameSubst :: Eq v => (v -> v) -> Term v -> Term v
applyNameSubst s (Var x)   = Var $ s x
applyNameSubst s (App l r) = App (applyNameSubst s l) (applyNameSubst s r)
applyNameSubst s (Lam x t) = Lam x $ applyNameSubst s t

-- TODO use a state monad
uniqueify :: Term String -> Term String
uniqueify t = let (t', _, _) = helper t 0 empty
              in t'
  where helper (Var x)   i vs = (Var x, i, insert x vs)
        helper (App l r) i vs = let (l', i',  vs')  = helper l i  vs
                                    (r', i'', vs'') = helper r i' vs'
                                in (App l' r', i'', vs'')
        helper (Lam x t) i vs = let (x', i',  vs')  = freshen x i vs
                                    (t', i'', vs'') = helper (applyNameSubst (subst x x') t) i' vs'
                                in (Lam x' t', i'', vs'')
        freshen x i vs = if member x vs
                            then freshen (x ++ "$" ++ show i) (i + 1) vs
                            else (x, i, insert x vs)

applySubst :: Eq v => (v -> Term v) -> Term v -> Term v
applySubst s (Var x)   = s x
applySubst s (App l r) = App (applySubst s l) (applySubst s r)
applySubst s (Lam x t) = Lam x $ applySubst s t

evalValueNF :: (Eq v) => (v -> Term v) -> Term v -> Term v
evalValueNF env (Var x)   = env x
evalValueNF env (App l r) = 
  let r' = evalValueNF env r -- evaluate argument first => call-by-value.
  in case evalValueNF env l of 
          (Lam x t) -> evalValueNF (\ y -> if y == x then r' else env y) t -- substitute the evaluated argument for its name
                                                                           -- inside the body and evaluate.
          l'        -> App l' r'
evalValueNF env (Lam x t) = Lam x $ evalValueNF (\ y -> if y == x then Var x else env y) t -- evaluate under lambdas, to get normal form.
                                                                                           -- don't use previous bindings for x
                                                                                           -- inside the body.

evalValueNFTop :: Term String -> Term String
evalValueNFTop = evalValueNF emptyEnv . uniqueify
  where emptyEnv x = Var x

evalValueWHNF :: Eq v => (v -> Term v) -> Term v -> Term v
evalValueWHNF env (Var x)   = env x
evalValueWHNF env (App l r) = 
  let r' = evalValueWHNF env r -- evaluate argument first => call-by-value.
  in case evalValueWHNF env l of 
          (Lam x t) -> let env' y = if y == x then r' else env y 
                       in evalValueWHNF env $ applySubst env' t -- substitute the evaluated argument for its name
                                                                -- inside the body and evaluate.
          l'        -> App l' r'
evalValueWHNF env t = t -- don't evaluate under lambdas, to get weak head normal form.

evalValueWHNFTop :: Term String -> Term String
evalValueWHNFTop = evalValueWHNF emptyEnv . uniqueify
  where emptyEnv x = Var x

data DBTerm v = DBVar v                     -- named variables,      like 0
              | DBLam (DBTerm v)            -- lambda terms,         like (\ (2 (1 0)))
              | DBApp (DBTerm v) (DBTerm v) -- function application, like (1 0)

deriving instance Show v => Show (DBTerm v)
deriving instance Eq v => Eq (DBTerm v)
deriving instance Functor DBTerm

toDeBruijn :: Term String -> DBTerm Int
toDeBruijn t = helper (\ str -> error $ "no binding for " ++ str ++ " in " ++ show t) t
  where helper :: (String -> Int) -> Term String -> DBTerm Int
        helper s (Var x)   = DBVar $ s x
        helper s (App l r) = DBApp (helper s l) (helper s r)
        helper s (Lam x t) = let s' y = if y == x then 0 else succ . s $ y
                             in DBLam $ helper s' t

-- NOTE: This does not necessarily produce a term with unique names, just a term that
-- will behave correctly if shadowed bindings are respected.
fromDeBruijn :: DBTerm Int -> Term String
fromDeBruijn t = snd $ helper 0 t
  where helper i (DBVar x)   = (0, Var $ show x) -- so we correctly identify lambdas with no nested lambdas
        helper i (DBApp l r) = let (j, l') = helper i l
                                   (k, r') = helper i r
                               in (min j k, App l' r')
        helper i (DBLam t)   = let (j, t') = helper (succ i) t
                               in (succ j, Lam (show j) t')

shift :: Int -> Int -> DBTerm Int -> DBTerm Int
shift d c (DBVar x)   = DBVar $ if x >= c then d + x else x
shift d c (DBApp l r) = DBApp (shift d c l) (shift d c r)
shift d c (DBLam t)   = DBLam $ shift d (succ c) t

type DBSubst = M.Map Int (DBTerm Int)

dbApplySubst :: DBSubst -> DBTerm Int -> DBTerm Int
dbApplySubst s (DBVar x)   = lookupDBVar s x
dbApplySubst s (DBApp l r) = DBApp (dbApplySubst s l) (dbApplySubst s r)
dbApplySubst s (DBLam t)   = let s' = pushSubst (DBVar 0) (shiftSubst s)
                             in DBLam . dbApplySubst s' $ t

pushSubst :: DBTerm Int -> DBSubst -> DBSubst
pushSubst t = M.insert 0 t

shiftSubst :: DBSubst -> DBSubst
shiftSubst = M.map (shift 1 0) . M.mapKeys succ

lookupDBVar :: DBSubst -> Int -> DBTerm Int
lookupDBVar env x = M.findWithDefault (DBVar x) x env

dbEvalValueNF :: DBSubst -> DBTerm Int -> DBTerm Int
dbEvalValueNF env (DBVar x)   = lookupDBVar env x
dbEvalValueNF env (DBApp l r) = let r'   = dbEvalValueNF env r -- call-by-value, arg evaluated
                                    env' = pushSubst (shift 1 0 r') env
                                in case dbEvalValueNF env l of
                                        DBLam t -> dbEvalValueNF env -- evaluate after substitution in case we have
                                                                     -- exposed an application
                                                 $ shift (- 1) 0 $ dbApplySubst env' t
                                        l'      -> DBApp l' r'
dbEvalValueNF env (DBLam t)   = let env' = pushSubst (DBVar 0) . shiftSubst $ env
                                in DBLam $ dbEvalValueNF env' t -- go under lambdas to get normal form

dbEvalValueNFTop :: DBTerm Int -> DBTerm Int
dbEvalValueNFTop t = dbEvalValueNF emptyEnv t
  where emptyEnv = M.empty

dbEvalValueWHNF :: DBSubst -> DBTerm Int -> DBTerm Int
dbEvalValueWHNF env (DBVar x)   = lookupDBVar env x
dbEvalValueWHNF env (DBApp l r) = let r'   = dbEvalValueWHNF env r -- call-by-value, arg evaluated
                                      env' = pushSubst (shift 1 0 r') env
                                  in case dbEvalValueWHNF env l of
                                          DBLam t -> dbEvalValueWHNF env -- evaluate after substitution in case we have
                                                                         -- exposed an application
                                                   $ shift (- 1) 0 $ dbApplySubst env' t
                                          l'      -> DBApp l' r'
dbEvalValueWHNF env t           = t -- don't go under lambdas so we get weak head normal form

dbEvalValueWHNFTop :: DBTerm Int -> DBTerm Int
dbEvalValueWHNFTop t = dbEvalValueWHNF emptyEnv t
  where emptyEnv = M.empty

lambdaId    = Lam "x" (Var "x")
churchZero  = Lam "f" lambdaId
churchSucc  = Lam "c" (Lam "f" (Lam "x" (App (Var "f") (App (App (Var "c") (Var "f")) (Var "x")))))
churchOne   = App churchSucc churchZero
churchTwo   = App churchSucc churchOne
churchThree = App churchSucc churchTwo

capture = Lam "x" (Lam "x" (Var "x"))
capturex = (App capture (Var "y"))

tru = Lam "t" (Lam "f" (Var "t"))  -- same as const
fls = Lam "t" (Lam "f" (Var "f"))  -- same as churchZero

test = Lam "l" $ Lam "m" $ Lam "n" $ App (App (Var "l") (Var "m")) (Var "n")

and = Lam "b" $ Lam "c" $ App (App (Var "b") (Var "c")) fls

or = Lam "b" $ Lam "c" $ App (App (Var "b") tru) (Var "c")

terms = [ lambdaId
        , churchZero
        , churchSucc
        , churchOne
        , churchTwo
        , churchThree
        , capture
        , capturex
        , tru
        , fls
        , test
        , UntypedLambdaCalculus.and
        , UntypedLambdaCalculus.or
        ]
