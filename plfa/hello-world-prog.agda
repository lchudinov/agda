{-# OPTIONS --guardedness #-}

module hello-world-prog where
  
open import IO

main : Main
main = run (putStrLn "Hello, world!")

-- agda --compile hello-world-prog.agda
-- agda --js hello-world-prog.agda
  