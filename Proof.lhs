\documentclass[a4paper,11pt]{article}

\usepackage{minted}
\newminted[code]{haskell}{}
\newcommand\hsin[1]{\mintinline{haskell}{#1}}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{tikz}

\usepackage[margin=3cm]{geometry}

\begin{document}

\appendix

\section{Annotated Source Code}

This appendix is a literate Haskell file, which is a Haskell source file that is
also a valid latex document. This source file is \verb+Proof.lhs+, which is
responsible for carrying out the automated proof for each square. Other modules
in the program are responsible for parsing the input templates and breaking them
down into individual squares, and also creating the output report as a pdf, but
it is this module that is crucial for the correctness of the proof. The full
source code of the program is available at \ref{FIXME}.

All of the Haskell code in the module will appear as inline listings in the
document. For
example, the following code is the preamble of the module that imports the
libraries that we will be using.


\begin{code}
module Proof where

import Data.SBV
import Data.Matrix
import Control.Monad
import GHC.Generics

\end{code}

\paragraph{\bf A quick introduction to Haskell.}

In Haskell function application is written using spaces. So calling a function
$f(x+1,y+2)$ would be written as \hsin{f (x + 1) (y + 2)}. 
The \hsin{$} operator implements function application, so \hsin{f $ a} means
``apply function \verb+f+ to argument \verb+a+. 
The \hsin{$} operator is often used to remove brackets from expressions,
so instead of writing \hsin{f (x + 1)} we can instead write \hsin{f $ x + 1}.

The syntax \hsin{f :: Int -> Float -> String} is a type annotation that denotes
that \hsin{f} is a two argument function that takes an \hsin{Int} as its first
argument, a \hsin{Float} as its second argument, and it returns a \hsin{String}.
The following example defines a two argument function that takes two integers
and returns their sum.

\begin{code}
example :: Int -> Int -> Int
example x y = x + y
\end{code}

There are many resources available online if more information on Haskell
syntax is desired.

\paragraph{\bf Introduction to the SBV library.}

The Haskell SBV library allows us to write programs in Haskell and then prove
theorems about those programs using an SMT solver. This will allow us to
succinctly specify the input to the solver as a readable and checkable Haskell
program, rather than a very long and unreadable SMT formula.

We will construct an SMT formula over the algebraic real numbers, which is
represented by the \hsin{SReal} type in SBV. It is important to understand that
the SMT solver will genuinely verify the correctness of the formula over the set
of algebraic reals. So there will be no approximations or rounding errors to
worry about in the proof.

As a first example, the following code uses SBV to attempt to prove the formula
\begin{equation*}
\forall x \cdot (x > 0 \Rightarrow x^2 \ne 2),
\end{equation*}
which states that there is no positive square root of two.

\begin{code}
noRootTwo :: IO ThmResult
noRootTwo = prove $ do
    x <- symbolic "x" :: Symbolic SReal
    return $ x .> 0 .=> x * x ./= 2
\end{code}

The first line defines \hsin{x} to be a symbolic algebraic real variable, and
the second line then directly constructs the formula in terms of \hsin{x}. Note
that when we use the \hsin{SReal} type, we must prefix all of our comparison
operators with a \hsin{.} symbol, so the usual Haskell not-equal operator
\hsin{/=} becomes \hsin{./=}.

The formula is clearly false, and so when we run the proof we get the following
output.
\begin{verbatim}
ghci> noRootTwo 
Falsifiable. Counter-example:
  x = root(2, x^2 = 2) = 1.414213562373095... :: Real
\end{verbatim}
Here the SMT solver identifies that the formula is false, and gives a counter
example, which is of course $\sqrt{2}$. Note that the answer is given
symbolically.

If we configure SBV to print out its interaction with the solver, then the
following interaction is produced.

\begin{verbatim}
[GOOD] ; --- literal constants ---
[GOOD] (define-fun s1 () Real 0.0)
[GOOD] (define-fun s5 () Real (/ 2.0 1.0))
[GOOD] ; --- skolem constants ---
[GOOD] (declare-fun s0 () Real) ; tracks user variable "x"
[GOOD] ; --- formula ---
[GOOD] (define-fun s2 () Bool (> s0 s1))
[GOOD] (define-fun s3 () Bool (not s2))
[GOOD] (define-fun s4 () Real (* s0 s0))
[GOOD] (define-fun s6 () Bool (distinct s4 s5))
[GOOD] (define-fun s7 () Bool (or s3 s6))
[GOOD] (assert (not s7))
[SEND] (check-sat)
[RECV] sat
\end{verbatim}

Here we can see that our formula has been translated into an SMT formula. Then
the SMT solver is asked to find a satisfying assignment of the formula's
negation. In this case it succeeds, meaning that our formula was false.


For a slightly more involved example, we will prove that Pythagoras's theorem is
true. We will use three symbolic points $p, q, r \in \mathbb{R}^2$. The following
function detects whether $\vec{pq}$ and $\vec{qr}$ form a right-angle, by
checking whether their cross product is zero. Note that this function returns an
\hsin{SBool}, which is a symbolic Boolean variable.

\begin{code}

rightAngle :: (SReal, SReal) -> (SReal, SReal) -> (SReal, SReal) -> SBool
rightAngle (p1, p2) (q1, q2) (r1, r2) = v1 * u1 + v2 * u2 .== 0
    where (v1, v2) = (p1 - q1, p2 - q2)
          (u1, u2) = (r1 - q1, r2 - q2)
\end{code}

The next function checks whether $a^2 + b^2 = c^2$ for the triangle
defined by $p, q,$ and $r$.

\begin{code}

pythagoras :: (SReal, SReal) -> (SReal, SReal) -> (SReal, SReal) -> SBool
pythagoras (p1, p2) (q1, q2) (r1, r2) = aSquared + bSquared .== cSquared
    where aSquared = (p1 - q1)^2 + (p2 - q2)^2
          bSquared = (q1 - r1)^2 + (q2 - r2)^2
          cSquared = (r1 - p1)^2 + (r2 - p2)^2
\end{code}

Finally, we can ask SBV to prove the theorem. Here we define six symbolic
variables that encode the coordinates of $p$, $q$, and $r$, and then we encode a
formula that states that if $p$, $q$, and $r$ form a right-angled triangle, then
the conclusion of Pythagoras's theorem must hold.

\begin{code}

pythagorasProof :: IO ThmResult
pythagorasProof = prove $ do
    [p1, p2] <- symbolics ["p1", "p2"] 
    [q1, q2] <- symbolics ["q1", "q2"] 
    [r1, r2] <- symbolics ["r1", "r2"] 
    return $     rightAngle (p1, p2) (q1, q2) (r1, r2) 
             .=> pythagoras (p1, p2) (q1, q2) (r1, r2)

\end{code}

When we run the proof, the SMT solver verifies that Pythagoras's theorem is true.
 
\begin{verbatim}
ghci> pythagorasProof 
Q.E.D.
\end{verbatim}


\subsection{Our Proof}

We now turn to our own proof. The first few lines simply define the constants
that we will use in the proof.

\begin{code}

eps :: SReal
eps = 0.01

delta :: SReal
delta = 0.5

colorOffset :: SReal
colorOffset = 4
\end{code}

Next we define the types that will be used to input data into the proof. A
\hsin{RawPoint} contains a colour string that is 
one of \hsin{"red"}, \hsin{"orange"}, \hsin{"black"}, \hsin{"green"}, or
\hsin{"blue"}, and a direction string that is one of \hsin{"up"}, \hsin{"down"},
\hsin{"left"}, or \hsin{"right"}.

\begin{code}

data RawPoint = RawPoint
    { col :: String
    , dir :: String
    } deriving (Show, Eq, Generic)

\end{code}

A \hsin{RawSquare} contains four \hsin{RawPoints}, corresponding to the four
corners of the square. We will use \verb+zz+ as a suffix for the point at $(0,
0)$, \verb+zo+ as the suffix for the point at $(0, 1)$, \verb+oz+ as the suffix
for the point at $(1, 0)$, and \verb+oo+ as the suffix for the point at $(1,
1)$. 

\begin{code}

data RawSquare = RawSquare 
    { rzz :: RawPoint
    , rzo :: RawPoint
    , roz :: RawPoint
    , roo :: RawPoint
    } deriving (Show, Eq, Generic)
\end{code}

For example, consider the following square.
\begin{center}
\resizebox{0.3\textwidth}{!}{
\begin{tikzpicture}[scale=5]
\path[->,line width=1,black] (0.0, 0.0) edge (0.0, -8.0e-2);
\path[->,line width=1,black] (0.0, 0.2) edge (8.0e-2, 0.2);
\path[->,line width=1,black] (0.2, 0.0) edge (0.27999999999999997, 0.0);
\path[->,line width=1,black] (0.2, 0.2) edge (0.27999999999999997, 0.2);
\node [fill=black!100!white,circle,inner sep=2] at (0.0, 0.0)  {};
\node [fill=orange!100!white,circle,inner sep=2] at (0.0, 0.2)  {};
\node [fill=green!100!white,circle,inner sep=2] at (0.2, 0.0)  {};
\node [fill=green!100!white,circle,inner sep=2] at (0.2, 0.2)  {};
\end{tikzpicture}
}
\end{center}
This would be represented as the following value.


\begin{verbatim}
RawSquare { rzz = RawPoint {col = "black",  dir = "down"}
          , rzo = RawPoint {col = "orange", dir = "right"}
          , roz = RawPoint {col = "green",  dir = "right"}
          , roo = RawPoint {col = "green",  dir = "right"}
          }
\end{verbatim}

\paragraph{\bf Symbolic squares.}

Next we define two types that represent the continuous function that we will
build from the input data. The type \hsin{Point} contains four symbolic values:
\hsin{f} gives the value of the function at the point, \hsin{fx} gives the
gradient with respect to $x$ at the point, \hsin{fy} gives the gradient with
respect to $y$ at the point, and \hsin{fxy} gives the gradient with respect to
$x$ and $y$ at the point.

\begin{code}

data Point = Point
    { f   :: SReal
    , fx  :: SReal
    , fy  :: SReal
    , fxy :: SReal
    } deriving Show

\end{code}

A \hsin{Square} contains four symbolic points, one for each corner of the
square. We use the same naming convention as \hsin{RawSquare} for these points.

\begin{code}

data Square = Square
    { zz :: Point
    , zo :: Point
    , oz :: Point
    , oo :: Point
    } deriving Show

\end{code}

\paragraph{Converting raw squares into squares.}
The next section of code turns the input data into a symbolic square, following
the instructions given by the reduction from the paper. 

We begin by defining the five colors that we used
in the paper. We will represent the value of $f$ at each point of the square
symbolically. We will introduce five symbolic values \verb+red+, \verb+orange+,
\verb+black+, \verb+green+, and \verb+blue+. Then, if a point in the square is
red, we will represent the value of $f$ at that point as \verb/red + offset/,
where the offset is some number between 0 and 2. We will then quantify over all
values that satisfy \verb/red > orange + 4/, \verb/orange > black + 4/,
\verb/black > green + 4/, and \verb/green > blue + 4/. In this way, we are able
to show that the theorem holds no matter what particular values each color takes
within the square, so long as those values are sufficiently far apart.


The following functions define the offsets for each color. Each of them takes
\verb+x+ and \verb+y+ as inputs, which should both be assumed to belong to $\{0,
1\}$. The output is a number in $\{0, 1, 2, 3\}$ that describes how that color
behaves across the square. 

The red function increases as we move right and down.

\begin{code}

redGrad :: SReal -> SReal -> SReal
redGrad x y = x + (1-y)

\end{code}

The orange function increases as we go down or left.

\begin{code}

orangeGrad :: SReal -> SReal -> SReal
orangeGrad x y = (1-x) + (1 - y)

\end{code}

The black function increases as we go up or right.

\begin{code}

blackGrad :: SReal -> SReal -> SReal
blackGrad x y = x + y  

\end{code}

The green function is the same as the orange function, while the blue function is
the same as the red function, so we just reuse the implementations.

\begin{code}

greenGrad :: SReal -> SReal -> SReal
greenGrad = orangeGrad

blueGrad :: SReal -> SReal -> SReal
blueGrad = redGrad 

\end{code}

The \hsin{convertPotential} function takes a raw point, the list of symbolic
values 
\begin{verbatim}
[red, orange, black, green, blue],
\end{verbatim}
and an $x$ and $y$ coordinate
for the point. It outputs the symbolic value of $f$ at the point computed as we
describe above. 

\begin{code}

convertPotential :: RawPoint -> [SReal] -> SReal -> SReal -> SReal
convertPotential point vars x y = convert (col point)
    where convert "red"    = vars !! 0 + redGrad    x y
          convert "orange" = vars !! 1 + orangeGrad x y
          convert "black"  = vars !! 2 + blackGrad  x y
          convert "green"  = vars !! 3 + greenGrad  x y
          convert "blue"   = vars !! 4 + blueGrad   x y
          convert x        = error ("unable to parse color " ++ show x)

\end{code}


The \hsin{convertDirection} function converts the direction given by the raw
point into a gradient. It outputs a pair of symbolic values $(x', y')$, where
$x'$ is the gradient with respect to $x$, and $y'$ is the gradient with respect
to $y$. Recall from the paper that an arrow pointing upwards indicates that the
function \emph{decreases} as we move upwards, and does not move as we move left
or right.  Therefore this corresponds to
setting $x' = 0$ and $y' = -\delta$, where $\delta$ is the parameter indicating
how steep the function should be. The following function implements this, along
with the other three cases.

\begin{code}

convertDirection :: String -> (SReal, SReal)
convertDirection "up"    = ( 0, -delta)
convertDirection "down"  = ( 0,  delta)
convertDirection "right" = (-delta,  0)
convertDirection "left"  = ( delta,  0)

\end{code}

The next function converts a raw point to a symbolic point using the functions
defined above. It sets \hsin{f} to be the value of the potential at the point, it
sets \hsin{fx} and \hsin{fy} according to the gradients returned by
\hsin{convertDirection}, and it sets \hsin{fxy} to be zero. All of these are in
accordance with the reduction defined in the paper. 

\begin{code}


rawPointToPoint :: RawPoint -> [SReal] -> SReal -> SReal -> Point
rawPointToPoint point vars x y = Point
                            { f   = convertPotential point vars x y
                            , fx  = lr
                            , fy  = ud
                            , fxy = 0
                            }
    where (lr, ud) = convertDirection (dir point)

\end{code}

Finally, we can turn a raw square into a symbolic square. This function simply
converts each point of the raw square using the function above, while passing in
the appropriate coordinates. 


\begin{code}

rawSquareToSquare :: RawSquare -> [SReal] -> Square
rawSquareToSquare sq vars = Square
                            { zz = rawPointToPoint (rzz sq) vars 0 0
                            , zo = rawPointToPoint (rzo sq) vars 0 1
                            , oz = rawPointToPoint (roz sq) vars 1 0
                            , oo = rawPointToPoint (roo sq) vars 1 1
                            }

\end{code}


\paragraph{\bf Bicubic interpolation.}

Recall that the bicubic interpolation inside this square will be a polynomial of the
form:
\begin{equation}\label{eq:bicubic}
f(x,y) = \sum_{i=0}^3 \sum_{j=0}^3 a_{ij} x^i y^j
\end{equation}
where the coefficients $a_{ij}$ are computed as follows
\begin{align*}
&\begin{bmatrix}
a_{00} & a_{01} & a_{02} & a_{03}\\
a_{10} & a_{11} & a_{12} & a_{13}\\
a_{20} & a_{21} & a_{22} & a_{23}\\
a_{30} & a_{31} & a_{32} & a_{33}\\
\end{bmatrix}\\
&=
\begin{bmatrix}
1 & 0 & 0 & 0\\
0 & 0 & 1 & 0\\
-3 & 3 & -2 & -1\\
2 & -2 & 1 & 1\\
\end{bmatrix} \cdot 
\begin{bmatrix}
f(0,0) & f(0,1) & f_y(0,0) & f_y(0,1)\\
f(1,0) & f(1,1) & f_y(1,0) & f_y(1,1)\\
f_x(0,0) & f_x(0,1) & f_{xy}(0,0) & f_{xy}(0,1)\\
f_x(1,0) & f_x(1,1) & f_{xy}(1,0) & f_{xy}(1,1)\\
\end{bmatrix}
\cdot
\begin{bmatrix}
1 & 0 & -3 & 2\\
0 & 0 & 3 & -2\\
0 & 1 & -2 & 1\\
0 & 0 & -1 & 1\\
\end{bmatrix}\nonumber
\end{align*}

The following code implements this. We will use the \verb+matrix+ library to do
the matrix multiplications. We first define \hsin{RealMatrix} to be a matrix
type that holds symbolic values, and we then define the two constant matrices
seen above.

\begin{code}

type RealMatrix = Matrix SReal

leftMatrix :: RealMatrix
leftMatrix = fromList 4 4 [  1,  0,  0,  0
                          ,  0,  0,  1,  0
                          , -3,  3, -2, -1
                          ,  2, -2,  1,  1
                          ]

rightMatrix :: RealMatrix 
rightMatrix = fromList 4 4 [ 1, 0, -3,  2
                           , 0, 0,  3, -2
                           , 0, 1, -2,  1
                           , 0, 0, -1,  1
                           ]

\end{code}

Next we define the \hsin{bicubic} function that takes a square and outputs the
coefficient matrix, using the formula above. 

\begin{code}

bicubic :: Square -> RealMatrix
bicubic (Square zz zo oz oo) = leftMatrix * pointMatrix * rightMatrix 
    where pointMatrix = fromList 4 4 [ f  zz, f  zo, fy  zz, fy  zo
                                     , f  oz, f  oo, fy  oz, fy  oo
                                     , fx zz, fx zo, fxy zz, fxy zo
                                     , fx oz, fx oo, fxy oz, fxy oo
                                     ]

\end{code}

Finally we provide two functions to extract the derivative of $f(x, y)$ with
respect to $x$ and with respect to $y$. These two functions take the coefficient
matrix computed by \hsin{bicubic}, an $x$ coordinate and a $y$ coordinate, and
output the gradient at that point. 

For the $x$ derivative, we 
observe that for a fixed value of $y$, we have that 
\begin{equation*}
f(x, y) = c_3 x^3 + c_2 x^2 + c_1 x + c_0
\end{equation*}
where $(c_0, c_1, c_2, c_3) = A \cdot (1, y, y^2, y^3)^T$ and $A$ is the matrix
of coefficients. Therefore the $x$ derivative at this point is $3 c_3 x^2
+ 2 c_2 x + c_1$.

\begin{code}

xDerivative :: RealMatrix -> SReal -> SReal -> SReal
xDerivative interpolation x y = 3*c3*x^2 + 2*c2*x + c1
    where yVec = fromList 4 1 [1, y, y^2, y^3]
          [c0, c1, c2, c3] = toList (interpolation * yVec)

\end{code}

Similarly, for a fixed value of $x$ we have that 
\begin{equation*}
f(x, y) = c_3 y^3 + c_2 y^2 + c_1 y + c_0
\end{equation*}
where $(c_0, c_1, c_2, c_3)^T = (1, x, x^2, x^3) \cdot A$ and $A$ is the matrix
of coefficients. Therefore the $y$ derivative at this point is $3 c_3 y^2
+ 2 c_2 y + c_1$.

\begin{code}

yDerivative :: RealMatrix -> SReal -> SReal -> SReal
yDerivative interpolation x y = 3*c3*y^2 + 2*c2*y + c1
    where xVec = fromList 1 4 [1, x, x^2, x^3]
          [c0, c1, c2, c3] = toList (xVec * interpolation)

\end{code}

\paragraph{\bf The proof.}
We are now ready to specify the formula that we will present to the SMT solver. 
We begin by specifying the constraints that will be used in the formula.

The following function checks that a symbolic value lies in $[0, 1]$. We will
use this to ensure that the symbolic point $(x, y)$ lies in the $[0, 1]^2$
square. 

\begin{code}

inSquare :: SReal -> SBool
inSquare x = (x .>= 0) .&& (x .<= 1)
\end{code}

The next constraint enforces the constraints on the symbolic values for the
colors, which we described earlier. It takes the list of symbolic values
\hsin{[red, orange, black, green, blue]}, and checks that all of the values are
suitably far apart (\verb+colorOffset+ was defined to be 4 earlier on in the
file).

\begin{code}

colorConstraints :: [SReal] -> SBool
colorConstraints vars =  vars !! 0 .> vars !! 1 + colorOffset
                     .&& vars !! 1 .> vars !! 2 + colorOffset
                     .&& vars !! 2 .> vars !! 3 + colorOffset
                     .&& vars !! 3 .> vars !! 4 + colorOffset

\end{code}

Next we specify a list of tautologies. Note that each statement in the list is
unconditionally true. We introduce these because, without them, the SMT solver
does not verify the formula within a reasonable amount of time. So, we modify
our formula from ``if A then B'', to ``if A and T then B'', where T is a
tautology. Since the solver, at its core, is based on the DPLL algorithm, this
in effect suggests a possible case analysis to the solver, which in practice
dramatically speeds up the proof. Indeed, these tautologies were derived from
our own experience with useful cases when we proved the theorem for some of the
squares by hand. 

Unfortunately we did not find one single tautology that worked for all of the
squares. So here we give three possibilities. For each square we will try the
proof with each of the tautologies, and we will consider the square to be
verified if the solver terminates with at least one tautology.

\begin{code}

tautologies :: SReal -> SReal -> [SBool]
tautologies x y = [ x .>= y   .|| y   .>= x 
                  , y .>= 0.5 .|| 0.5 .>= y 
                  , x .>= 0.5 .|| 0.5 .>= x 
                  ]

\end{code}

Now we specify the conclusion of the proof. We want to prove that no
$\varepsilon$-stationary points exist within the square, which means that
at each
point $(x, y)$ in the interpolated square, it is not the case that both the $x$
derivative and the $y$ derivative are within $\epsilon$ of zero. 
The \hsin{nonZeroGradient} function takes the matrix of coefficients from the
interpolation, and a symbolic point $(x, y)$ as arguments. It computes the $x$
derivative and the $y$ derivative, and returns true if the gradients
satisfy the condition.

\begin{code}

notEpsClose :: SReal -> SBool
notEpsClose x = (x .< -eps) .|| (x .> eps)


nonZeroGradient :: RealMatrix -> SReal -> SReal -> SBool
nonZeroGradient interpolation x y = notEpsClose (xDerivative interpolation x y) 
                                .|| notEpsClose (yDerivative interpolation x y) 

\end{code}

Finally we have the main proof function. This function takes as input a raw
square, and a number $t$ between 0 and 2 indicating which tautology we would like to
use. This function defines the symbolic
values for the potentials, as well as a symbolic point $(x, y)$. In then asks
the SMT solver to prove the formula ``if the colour constraints hold, and $(x,
y)$ is in the $[0, 1]^2$ square, and tautology $t$ holds, then 
the gradient is not less than or equal to $\epsilon$ at $(x, y)$''. 

\begin{code}

proof :: RawSquare -> Int -> IO ThmResult
proof raw tautologyIdx = prove $ do
        setTimeOut 1000
        vars   <- symbolics ["red", "orange", "black", "green", "blue"]
        [x, y] <- symbolics ["x", "y"]
        let inter     = bicubic $ rawSquareToSquare raw vars
            tautology = tautologies x y !! tautologyIdx
        return $     colorConstraints vars 
                 .&& inSquare x 
                 .&& inSquare y 
                 .&& tautology
                 .=> nonZeroGradient inter x y

\end{code}



\paragraph{\bf Dealing with proof output.}

The proof returns a \hsin{ThmResult} that tells us the output of the solver. The
following three functions tell us whether the SMT solver was successful or timed
out, and in the case where it was successful, whether it proved or disproved the
theorem. 

\begin{code}

successful :: ThmResult -> Bool
successful (ThmResult (Unknown _ _)) = False
successful (ThmResult (ProofError _ _ _)) = False
successful _ = True

proved :: ThmResult -> Bool
proved result = not $ modelExists result

disproved :: ThmResult -> Bool
disproved result = modelExists result

\end{code}


The following function verifies whether the theorem holds for a particular
square. It runs \hsin{proof} three times, once for each tautology. It then checks
whether any of those runs succeed, and if any run did succeed it returns the
\hsin{ThmResult} from that run. 

\begin{code}

verifySquare :: RawSquare -> IO ThmResult
verifySquare square = do
    results <- mapM (proof square) [0..2]
    let finished = filter successful results
    when (any proved finished && any disproved finished) $ 
        error "solver returned inconsistent results!"
    return $ if not . null $ finished then head finished
                                      else head results

\end{code}

\paragraph{\bf The boundary constraints.}

When a square lies on the boundary of the instance, there are extra constraints
to check on the boundary of the square. Specifically, in addition to satisfying
the theorem checked by \hsin{verifySquare}, we must also check that the 
direction that we follow as we decrease the gradient does not move us outside
the instance.
The following functions verify this condition, and they will be applied to  any square that lies on the boundary of the instance. 

We first define the \hsin{BoundarySide} type that encodes which side of the
instance the square touches. For the four corners squares, which lie on two sides
simultaneously, we will run the proof twice, once for each side. 

\begin{code}

data BoundarySide = BoundaryLeft 
                  | BoundaryRight 
                  | BoundaryBottom 
                  | BoundaryTop
                  deriving (Show, Eq)
\end{code}

In this setting, we only care about the points that lie directly on
the boundary. So, for a square that lies on the left side of the instance, we
only need to consider the points $(x, y)$ satisfying $x = 0$, and for those on
the right side of the instance we only consider the points satisfying $x = 1$.
The following function returns true for any point that lies directly on a given
boundary of the instance. 

\begin{code}

sideConstraint :: BoundarySide -> SReal -> SReal -> SBool
sideConstraint BoundaryLeft   x _ = x .== 0 
sideConstraint BoundaryRight  x _ = x .== 1
sideConstraint BoundaryBottom _ y = y .== 0
sideConstraint BoundaryTop    _ y = y .== 1

\end{code}

If a point lies on the boundary, we want the gradient to be larger than
$\epsilon$, while also not causing gradient descent to walk directly outside the
instance. For a point on the left boundary of the instance, it is sufficient to
check that either the $y$ gradient has magnitude larger than $\epsilon$, or that
the $x$ gradient is \emph{negative} and less than $-\epsilon$. In the latter
case, this ensures that gradient descent will walk into the instance, rather
than outside the boundary.

The following function takes as arguments the boundary side, the x gradient, and
the y gradient, and implements the appropriate check for the side that we are
on.

\begin{code}

sideTheorem :: BoundarySide -> SReal -> SReal -> SBool
sideTheorem BoundaryLeft   x' y' = x' .< -eps .|| y' .< -eps .|| y' .> eps
sideTheorem BoundaryRight  x' y' = x' .>  eps .|| y' .< -eps .|| y' .> eps
sideTheorem BoundaryBottom x' y' = y' .< -eps .|| x' .< -eps .|| x' .> eps
sideTheorem BoundaryTop    x' y' = y' .>  eps .|| x' .< -eps .|| x' .> eps
\end{code}

Finally, we can implement the proof for the boundary. The following function is
similar to the \hsin{proof} function, but now we check the formula ``if (x, y)
is in the square and lies on the given boundary of that square, and the colour constraints
hold, then the gradients must satisfy \hsin{sideTheorem}''.
Fortunately, we do not need any tautologies for the SMT solver to prove this
theorem. 

\begin{code}

boundaryProof :: RawSquare -> BoundarySide -> IO ThmResult
boundaryProof raw side = prove $ do
        setTimeOut 1000
        vars   <- symbolics ["red", "orange", "black", "green", "blue"]
        [x, y] <- symbolics ["x", "y"]
        let inter = bicubic $ rawSquareToSquare raw vars
            xGrad = xDerivative inter x y
            yGrad = yDerivative inter x y
        return $     sideConstraint side x y 
                 .&& colorConstraints vars 
                 .&& inSquare x 
                 .&& inSquare y 
                 .=> sideTheorem side xGrad yGrad   


\end{code}

\end{document}
