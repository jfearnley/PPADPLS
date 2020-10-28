module Parse (fullParse, allSquares, extractSquare, Templates, RawPointMap) where

import Data.List
import Data.List.Split
import qualified Data.Yaml as Y
import qualified Data.Map.Strict as M

import Proof

-- This module is responsible for parsing the input from a YAML file into the
-- list of squares that will be fed into the solver.

instance Y.ToJSON   RawPoint
instance Y.FromJSON RawPoint

instance Y.ToJSON   RawSquare
instance Y.FromJSON RawSquare

type Template     = M.Map String String
type Templates    = M.Map String RawPointMap
type RawPointMap  = M.Map (Int, Int) RawPoint
type RawSquareMap = M.Map String [RawSquare]



---- Parsing gadgets

-- Take a single line of a template specification as a string and parse it into
-- data structures that can be stored in a RawPointMap
parseLine :: [String] -> ((Int, Int), RawPoint)
parseLine [x, y, color, direction] = ((read x, read y), RawPoint color direction)

-- Parse an entire template into a RawPointMap
parseGadget :: String -> RawPointMap
parseGadget s = M.fromList . map parseLine . chunksOf 4 . words $ s


---- Extracting squares
-- This code takes a template, and outputs all distinct squares that appear in
-- that template


-- Extract a square from a template whose bottom left corner has 
-- coordinates (x, y)
extractSquare :: RawPointMap -> Int -> Int -> RawSquare
extractSquare points x y = RawSquare zz zo oz oo
    where zz = points M.! (x  , y  )
          zo = points M.! (x  , y+1)
          oz = points M.! (x+1, y  )
          oo = points M.! (x+1, y+1)

-- Extract all distinct squares from a template by extracting all possible
-- squares and then using the nub function to determine the distinct squares in
-- the template
allSquares :: RawPointMap -> [RawSquare]
allSquares points = nub squares
    where maxX = maximum . map fst . M.keys $ points
          maxY = maximum . map snd . M.keys $ points
          squares = [extractSquare points x y | x <- [0 .. maxX - 1],
                                                y <- [0 .. maxY - 1]]

-- Extracts all squares that lie on the boundary of a given template, with each
-- one annotated by the boundary on which they lie
allBoundarySquares :: RawPointMap -> [(RawSquare, BoundarySide)]
allBoundarySquares points = nub $ left ++ right ++ bottom ++ top
    where maxX = maximum . map fst . M.keys $ points
          maxY = maximum . map snd . M.keys $ points
          left   = [(extractSquare points x y, BoundaryLeft) 
                        | x <- [0],             y <- [0 .. maxY - 1]]
          right  = [(extractSquare points x y, BoundaryRight) 
                        | x <- [maxX - 1],      y <- [0 .. maxY - 1]]
          bottom = [(extractSquare points x y, BoundaryBottom) 
                        | x <- [0 .. maxX - 1], y <- [0]]
          top    = [(extractSquare points x y, BoundaryTop) 
                        | x <- [0 .. maxX - 1], y <- [maxY - 1]]


---- Parsing 

-- Parse a YAML file into a a set of templates
parse :: String -> IO Templates
parse fname = do
    yaml <- Y.decodeFileEither fname :: IO (Either Y.ParseException Template)
    case yaml of 
        Left exp      -> do putStrLn $ Y.prettyPrintParseException exp 
                            error "parse failure"
        Right gadgets -> return $ parseGadget <$> gadgets



-- Given a YAML file and a string identifying the boundary template, return the
-- list of templates, a list of every distinct square in each template, and a
-- list of all squares that lie on the boundary of the boundary template
fullParse :: String -> String -> 
                    IO (Templates, [RawSquare], [(RawSquare, BoundarySide)])
fullParse fname boundaryName = do
    templates <- parse fname
    let squares  = nub . concat . M.elems $ allSquares <$> templates
        bSquares = allBoundarySquares $ templates M.! boundaryName
    return (templates, squares, bSquares)

