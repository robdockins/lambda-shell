
import qualified Env as Env
import Lambda
import LambdaSearchTree

type Lam = PureLambda ()
lam = Lam ()
app = App ()
var = Var ()

t1 = app (lam "x" (var 0)) (var 0)
t2 = lam "z" (lam "x" (app (var 1) (var 2)))

initEnv = Env.insert "y" Env.empty

t3 = lamSubst (lam "v" (var 0)) 0 t2

-- reduction of this term does not terminate
ylam = let z = (lam "x" (app (var 0) (var 0))) in app z z

main = do putStrLn $ unlines $ map show $ lamEvalTrace (lam "y" (app t2 t1))
          putStrLn $ show $ lamEval     (lam "y" (app t2 t1))
          putStrLn $ show $ lamEvalMemo (lam "y" (app t2 t1))