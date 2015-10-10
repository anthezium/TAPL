import Test.QuickCheck
import Test.QuickCheck.Property (counterexample)

import UntypedLambdaCalculus

equivModuloDeBruijn f g = [ (toDeBruijn . f, g . toDeBruijn) ]
idempotent f = [ (toDeBruijn . f . f, toDeBruijn . f) ]
dbIdempotent f = [ (f . f . toDeBruijn, f . toDeBruijn) ]
toFrom1To1 = [ (toDeBruijn . fromDeBruijn . toDeBruijn, toDeBruijn) ]

termProps = concatMap g terms
  where f t (f1, f2) = let t1 = f1 t
                           t2 = f2 t
                       in counterexample ( "original term: " ++ show t ++ "\n"
                                        ++ "result 1: " ++ show t1 ++ "\n" 
                                        ++ "result 2: " ++ show t2) 
                                       $ t1 == t2
        g t = map (f t)
            $  equivModuloDeBruijn evalValueNFTop   dbEvalValueNFTop
            ++ equivModuloDeBruijn evalValueWHNFTop dbEvalValueWHNFTop
            ++ idempotent evalValueNFTop
            ++ idempotent evalValueWHNFTop
            ++ dbIdempotent dbEvalValueNFTop
            ++ dbIdempotent dbEvalValueWHNFTop
            ++ toFrom1To1

main :: IO ()
main = mapM_ quickCheck $ termProps 
