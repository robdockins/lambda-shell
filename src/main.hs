import System.Environment
import LambdaCmdLine

main :: IO ()
main = getArgs >>= lambdaCmdLine

