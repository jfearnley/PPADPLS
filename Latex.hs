module Latex where

import Data.List

-- This module contains various helper functions for building latex documents
-- programatically.

document :: String -> String
document document = unlines 
    [ "\\documentclass[a4paper]{article}"
    , "\\usepackage{tikz}"
    , "\\usepackage{graphicx}"
    , "\\title{The Complexity of Gradient Descent: \\\\CLS = PPAD $\\cap$ PLS \\\\ Proof Report}"
    , "\\date{}"
    , "\\begin{document}"
    , document
    , "\\end{document}"
    ]

section :: String -> String
section x = "\\section*{" ++ x ++ "}"

itemize :: [String] -> String
itemize items = unlines 
    [ "\\begin{itemize}"
    , concatMap ("\\item " ++) items
    , "\\end{itemize}"
    ]

tikz :: String -> [String] -> String
tikz size drawings = unlines 
    [ "\\resizebox{" ++ size ++ "\\textwidth}{!}{"
    , "\\begin{tikzpicture}[scale=5]"
    , unlines drawings
    , "\\end{tikzpicture}"
    , "}"
    ]


line :: String -> String -> String -> String 
line x y col = "\\path[" ++ col ++ "] " ++ x ++ " edge " ++ y ++ ";" 

arrow :: String -> String -> String -> String -> String
arrow x y col thickness = "\\path[->,line width=" ++ thickness ++ "," ++ col ++ "] " ++ x ++ " edge " ++ y ++ ";"

node :: String -> String -> String-> String -> String
node col coord lab size = "\\node [fill=" ++ col ++ "!100!white,circle,inner sep=" ++ size ++ "] at " ++ coord ++ " " ++ " {" ++ lab ++ "};"

text :: String -> String -> String -> String
text t coord col = "\\node[" ++ col ++ "] at " ++ coord ++ " {" ++ t ++ "};"

box :: String -> String -> String -> String
box x y col = "\\draw[" ++ col ++ ",ultra thick,dashed] " ++ x ++ " rectangle " ++ y ++ ";"

verbatim :: String -> String
verbatim x = unlines [ "\\begin{verbatim}"
                     , x
                     , "\\end{verbatim}"
                     ]


center :: String -> String
center x = unlines [ "\\begin{center}"
                   , x
                   , "\\end{center}"
                   ]

