module Main where

import Parse
import Proof
import Latex
import Report

main = do
   (templates, squares, boundarySqs) <- fullParse "all-templates.yaml" "X-Full Boundary"
   putStrLn $ "Loaded " ++ show (length templates) ++ " templates"
   putStrLn $ "Found " ++ show (length squares) ++ " distinct squares"
   putStrLn $ "Running automated proof"

   results <- mapM verifySquare squares
   boundaryResults <- mapM (uncurry boundaryProof) boundarySqs 
   let mainResults     = zip3 [1..] squares     results
       boundaryResults = zip3 [1..] boundarySqs results
   report mainResults boundaryResults templates 

   putStrLn $ "Proof complete"
   putStrLn $ "Report written to report/report.tex"
