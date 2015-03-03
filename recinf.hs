
type Label = String

-- Types

data Prim = PBool Bool | PInt Int

type TyVarId = Int

data Ty = Prim
        | TyVar TyVarId
        | Fun Ty Ty
        | Record [(Label, Ty)]
        | Variant [(Label, Ty)]
  deriving (Eq)

data TyScm = Mono Ty | Kinded Kind Ty
  deriving (Eq)

data Kind = UKind | RecKind | VariKind
  deriving (Eq)

-- Expression

type Name = String

data Expr =
    VarRef Name
  | Literal Prim
  | Abs Name Expr
  | App Expr Expr
  | Let Name Expr Expr
  | RecNew [(Label, Expr)]
  | RecGet Expr String
  | RecSet Expr Label Expr
  | VariNew Label Expr
  | Case Expr [(Label, Expr)]

-- Unification

data TyEq = TyEq TyScm TyScm
type KindEnv = [(Name, Kind)]
data Subst = [(Name, 

type Constraints = ([TyEq], KindEnv, Subst, KindEnv)

klookup :: KindEnv -> Name -> Maybe (Kind, KindEnv)
klookup kindenv name = klookup' [] kindenv name
  where 
    klookup [] [] _ = None
    klookup head (s, k)::rest name =
      if s = name
        Just (k, head ++ rest)
      else
        klookup (s, k):head rest name

unify :: Constraints -> Maybe Constraints

unify ([], kindenv1, subst, kindenv2) =
  Just ([], kindenv1, subst, kindenv2)

unify ((ts1, ts2):tyeqs, kindenv1, subst, kindenv2) =
  if ts1 = ts2
    unify (tyeqs, kindenv1, subst, kindenv2)
  else
    case (ts1, ts2) of
      (TyVar id1, TyScm) ->
        do (k,  = klookup 
        let ss = Subst [(ts2, TyVar id1)] in 
          Just (subst tyeqs ss,
                subst 
      


-- Inference

data TyEnv = 

data Program = (KindEnv, TyEnv, Expr)

infer :: Program -> Program
infer kindenv tyenv (VarRef name) = undefined

infer kindenv tyenv (Literal Prim) = undefined

infer kindenv tyenv (Abs name bodyExpr) =
  let (k1, s1, t1) = infer (():kindend

-- Main

main = print "ok"

{-

4章
- 型スキーマ＝型変数を含んだ型
- Subst(型の代入) ＝ (型変数の有限集合 -> 型スキーマ)
  S+ :: 型変数全体 -> 型スキーマ
  S^ :: 型スキーマ -> 型スキーマ

o 種類付き等式集合＝(K, E)
   K : 種類環境
   E : Kの下で整合的な型の等式

-}
