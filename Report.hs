module Report (report) where

import Proof
import Parse
import Latex

import Data.SBV
import Debug.Trace
import Data.List
import qualified Data.Map as M
import qualified Data.Yaml as Y

-- This module is responsible for taking the output of the proof and creating
-- the latex proof report

type SolverOutput = [(Int, RawSquare, ThmResult)] 
type BoundaryOutput = [(Int, (RawSquare, BoundarySide), ThmResult)] 

---- Drawing squares with tikz
-- The functions below create a tikz diagram that represent a single
-- square that was extracted from a template

coord :: Int -> Int -> String
coord x y = "(" ++ show x' ++ ", " ++ show y' ++ ")"
    where x' = fromIntegral x / 5
          y' = fromIntegral y / 5

coord' :: Double -> Double -> String
coord' x y = "(" ++ show x' ++ ", " ++ show y' ++ ")"
    where x' = x / 5
          y' = y / 5

tikzNode :: RawPoint -> Int -> Int -> String
tikzNode point x y = node (col point) (coord x y) "" "2"


direction :: Int -> Int -> String -> (Double, Double)
direction x y "up"   = (fromIntegral x, fromIntegral y+0.40)
direction x y "down" = (fromIntegral x, fromIntegral y-0.40)
direction x y "left" = (fromIntegral x-0.40, fromIntegral y)
direction x y "right" = (fromIntegral x+0.40, fromIntegral y)

tikzArrow :: RawPoint -> Int -> Int -> String
tikzArrow point x y = arrow from to "black" "1"
    where (x', y') = direction x y (dir point)
          from = coord x  y
          to   = coord' x' y'


tikzSquare :: RawSquare -> String
tikzSquare square = tikz "0.4" [ tikzArrow (rzz square) 0 0
                               , tikzArrow (rzo square) 0 1
                               , tikzArrow (roz square) 1 0
                               , tikzArrow (roo square) 1 1
                               , tikzNode (rzz square) 0 0
                               , tikzNode (rzo square) 0 1
                               , tikzNode (roz square) 1 0
                               , tikzNode (roo square) 1 1
                               ]

---- Creating the latex report for each square

squareReport :: (Int, RawSquare, ThmResult) -> String
squareReport (idx, square, result) = 
    unlines [ section $ "Square " ++ show idx
            , "\\vskip 1cm"
            , center $ tikzSquare square 
            , "\\vskip 2cm"
            , "\\noindent Solver reported:" ++ verbatim (show result)
            , "\\newpage"
            ]


---- Creating the latex report for each boundary square

boundaryReport :: (Int, (RawSquare, BoundarySide), ThmResult) -> String
boundaryReport (idx, (square, side), result) = 
    unlines [ section $ "Boundary Square " ++ show idx
            , "\\vskip 1cm"
            , center $ tikzSquare square 
            , "\\vskip 2cm"
            , "\\noindent Checked on " ++ show side ++ "\n"
            , "\\noindent Solver reported:" ++ verbatim (show result)
            , "\\newpage"
            ]



---- Drawing templates in tikz
-- The functions below create a tikz diagram that represent a single template

drawTemplateNode :: ((Int, Int), RawPoint) -> String
drawTemplateNode ((x, y), point) = tikzNode point x y

drawTemplateArrow :: ((Int, Int), RawPoint) -> String
drawTemplateArrow ((x, y), point) = tikzArrow point x y

drawTemplateNumber :: RawPointMap -> SolverOutput -> Int -> Int -> String
drawTemplateNumber template results x y = text (show idx) c color 
    where square = extractSquare template x y
          [(idx, _, res)] = filter (\(_, sq, _) -> sq == square) results
          c = coord' (fromIntegral x + 0.5) (fromIntegral y + 0.5) 
          color = if modelExists res then "red" else "black" 

drawTemplateNumbers :: RawPointMap -> SolverOutput -> String
drawTemplateNumbers template results = unlines output
    where maxX = maximum . map fst . M.keys $ template
          maxY = maximum . map snd . M.keys $ template
          output = [drawTemplateNumber template results x y 
                            | x <- [0..maxX-1], y <- [0..maxY-1]]

drawTemplate :: SolverOutput -> (String, RawPointMap) -> String
drawTemplate results (name, template) = unlines [ section name
                                                , "\\vskip 1cm"
                                                , diagram
                                                , "\\newpage"
                                                ]
    where points = unlines . map drawTemplateNode  . M.assocs $ template
          arrows = unlines . map drawTemplateArrow . M.assocs $ template
          diagram = tikz "1.0" [ arrows
                               , points
                               , drawTemplateNumbers template results
                               ]


drawTemplates :: SolverOutput -> Templates -> String
drawTemplates results templates = 
    intercalate "\\newpage" $ map (drawTemplate results) $ M.assocs templates

---- The title page

titlePage :: String -> String
titlePage preamble = 
    unlines [ "\\maketitle"
            , preamble
            , "\\paragraph{\\bf Parameters.} For this report, the following parameters were used."
            , itemize [ "eps = " ++ show eps
                      , "delta = " ++ show delta
                      , "color offset = " ++ show colorOffset
                      ]
            , "\\newpage"
            ]
                    

---- Creating the report

report :: SolverOutput -> BoundaryOutput -> Templates -> IO ()
report results boundaryResults templates = do
    preamble <- readFile "preamble.tex"
    let sReport = map squareReport   results
        bReport = map boundaryReport boundaryResults
        tReport = drawTemplates results templates
        latex   = document . unlines $ [titlePage preamble , tReport] 
                                       ++ sReport ++ bReport
    writeFile "report/report.tex" latex
