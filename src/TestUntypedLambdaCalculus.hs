import Test.QuickCheck

import UntypedLambdaCalculus

propCapture   = evalTop capturex  == Lam "x$0" (Var "x$0")
propChurchOne = evalTop churchOne == Lam "f" (Lam "x" (App (Var "f") (Var "x")))
propChurchTwo = evalTop churchTwo == Lam "f" (Lam "x" (App (Var "f") (App (Var "f") (Var "x"))))

main :: IO ()
main = mapM_ quickCheck [propCapture, propChurchOne, propChurchTwo]
