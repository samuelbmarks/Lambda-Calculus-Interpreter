module Interpreter where
import Control.Exception
import Debug.Trace
import Data.List

{-
---- Problem 1 ----

Applicative Order Reduction

E ::= x | \x.E1 | E1 E2

interpret(x) = x
interpret(\x.E1) =  if E1 containsRedex
                    then (\x. interpret(E1))
                    else \x.E1
interpret(E1 E2) =  if E1 containsRedex
                    then App (interpret(E1)) E2)
                    else  
                      (if E2 containsRedex
                      then E1 (interpret(E2))
                      else 
                        (if E1 isLambda
                        then substitute(E1 E2)
                        else (E1 E2))
                    )  

When interpreting a lambda expression, we want to check if
its expression E1 contains a redex. If it does, we will 
return a lambda expression with the interpreted internal
expression. If not, the expression cannot be reduced and 
the original lambda expression is returned.

When interpreting an application, we want to check if either
expression, E1 or E2, contains a redex. If E1 does, we will
return an application with the interpreted E1 and the original
E2. If not, we check the same condition for E2 and return an
application with E1 and the interpreted E2 if thats the case.
Otherwise, we perform a substitution of E2 on E1 only if E1
is a lambda expression. Finally, if none of these conditions
satisfy, the orginal expression is not a redex and cannot be
reduced.

Repeating these interpret steps will reduce the original
expression to normal form.

Below is the full implementation:
-}

---- Data types ----

type Name = String

data Expr = 
  Var Name
  | Lambda Name Expr
  | App Expr Expr
  deriving 
    (Eq,Show)


---- Functions ----

-- Contract: freeVars : Expr -> [Name]
-- Purpose: Finds free variables in expression expr
-- Example: freeVars (Lambda "x" (App (Var "x") (Var "y"))) returns ["y"]
-- Definition:
freeVars::Expr -> [Name]
freeVars expr =
  case expr of
    Var n -> [n]
    Lambda n e1 -> filter (/= n) (freeVars e1)
    App e1 e2 -> union (freeVars e1) (freeVars e2)

-- Contract: freshVars : [Expr] -> [Name]
-- Purpose: Returns a list of fresh variables (variables that are not free in the given list of expressions expr_li)
-- Example: freshVars [Lambda "1_" (App (Var "x") (App (Var "1_") (Var "2_")))] returns [1_,3_,4_,5_,..]
-- Definition:
freshVars::[Expr] -> [Name]
freshVars expr_li = listExcept (map (\x -> show x ++ "_") [1..]) (allFree expr_li)

-- Contract: allFree : [Expr] -> [Name]
-- Purpose: Returns a list of all the free variables present in a list of expressions expr_li
-- Example: allFree [Var "x",Var "y"] returns ["x","y"]
-- Definition:
allFree::[Expr] -> [Name]
allFree [] = []
allFree expr_li = 
  union (freeVars (head expr_li)) (allFree (tail expr_li))

-- Contract: listExcept : [Name] * [Name] -> [Name]
-- Purpose: Finds values in list l1 not in list l2 (like the set operation EXCEPT)
-- Example: listExcept ["1","2","3"] ["1","3"] returns ["2"]
-- Definition:
listExcept::[Name] -> [Name] -> [Name]
listExcept l1 [] = l1 
listExcept l1 l2 = listExcept (delete (head l2) l1) (tail l2)

-- Contract: subst : (Name,Expr) * Expr -> Expr
-- Purpose: Replaces all free occurrences of x in e2 with e1 (e2[e1/x])
-- Example: subst ("x",(Var "y")) (Lambda "z" (Var "x")) returns Lambda "1_" (Var "y")
-- Definition:
subst::(Name,Expr) -> Expr -> Expr 
subst (x,e1) e2 =
  case e2 of
    Var y -> if x == y then e1 else (Var y) 
    App expr1 expr2 -> (App (subst (x,e1) expr1) (subst (x,e1) expr2))
    Lambda y expr -> if x == y then (Lambda y expr) else 
      (Lambda (head (freshVars (expr:e1:(Var x):[]))) (subst (x,e1) (subst (y,(Var (head (freshVars (expr:e1:(Var x):[]))))) expr)))

-- Contract: appNF_OneStep : Expr -> Maybe Expr
-- Purpose: Finds the next applicative order redex in expr and performs a single step of reduction if possible
-- Example: appNF_OneStep (App (Lambda "x" (Var "x")) (Var "y")) returns Just (Var "y")
-- Definition:
appNF_OneStep::Expr -> Maybe Expr
appNF_OneStep expr =
  case expr of
    App expr1 expr2 ->
      if (containsRedex expr1) then Just (App (getJust (appNF_OneStep expr1)) expr2) else 
        (if (containsRedex expr2) then Just (App expr1 (getJust (appNF_OneStep expr2))) else 
          (if (containsRedex expr) then Just (subApp expr1 expr2) else Nothing))
    Lambda y expr1 ->
      if (containsRedex expr1) then Just (Lambda y (getJust (appNF_OneStep expr1))) else Nothing
    otherwise -> Nothing

-- Contract: containsRedex : Expr -> Bool
-- Purpose: Determines if an expression expr contains redex (reducible expression)
-- Example: containsRedex (App (Lambda "x" (Var "x")) (Var "y")) returns True
-- Definition:
containsRedex::Expr -> Bool
containsRedex expr = 
  case expr of
    App expr1 expr2 -> 
      case expr1 of
        Lambda _ _ -> True
        App e1 e2 -> 
          case e1 of
            Lambda _ _ -> True
            otherwise -> containsRedex e1 || containsRedex e2
        otherwise -> containsRedex expr2
    Lambda _ e -> containsRedex e
    Var _ -> False

-- Contract: subApp : Expr * Expr -> Expr
-- Purpose: Takes two expressions from an application and applies substitution
-- Example: subApp (Lambda "x" (Var "x")) (Var "y") returns Var "y"
-- Definition:
subApp::Expr -> Expr -> Expr
subApp expr1 expr2 = 
  case expr1 of
    Lambda y expr -> subst (y,expr2) expr

-- Contract: getJust : Maybe Expr -> Expr
-- Purpose: Returns the Expr value given a Maybe Expr value
-- Example: getJust (Just (Var "x")) returns Var "x"
-- Definition:
getJust::Maybe Expr -> Expr
getJust Nothing = (Var "null")
getJust (Just x) = x

-- Contract: appNF_n : Int * Expr -> Expr
-- Purpose: Performs n reductions (or as many as possible) on an expression expr
-- Example: appNF_n 1 (App (Lambda "x" (Var "x")) (Var "y")) returns Var "y"
-- Definition:
appNF_n::Int -> Expr -> Expr
appNF_n 0 expr = expr
appNF_n n expr =  if ((appNF_OneStep expr) == Nothing) 
                  then expr 
                  else appNF_n (n-1) (getJust (appNF_OneStep expr))


fun_a = 
  let
    x = 0
    fun_c f = let x = 1 in f x
    fun_d y = x + y
    fun_b = let x = 3 in (fun_c fun_d)
  in fun_b


tits = 
  let f (x:xs) = x : (f [ y | y <- xs, y `mod` x /= 0]) in f [2..]


ip::[Int] -> [Int] -> Int
ip [] [] = 0
ip a b = (head a) * (head b) + (ip (tail a) (tail b)) 
