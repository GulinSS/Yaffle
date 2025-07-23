module Compiler.CompileExpr

import public Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Evaluate
import Core.Options
import Core.TT

import Data.List
import Data.Maybe
import Data.SnocList
import Data.Vect

%default covering

data Args
    = NewTypeBy Nat Nat
    | EraseArgs Nat (List Nat)
    | Arity Nat

||| Extract the number of arguments from a term, or return that it's
||| a newtype by a given argument position
numArgs : Defs -> Term vars -> Core Args
numArgs defs (Ref _ (TyCon arity) n) = pure (Arity arity)
numArgs defs (Ref _ _ n)
    = do Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure (Arity 0)
         case definition gdef of
           DCon di _ arity =>
               case newTypeArg di of
                    Nothing => pure (EraseArgs arity (eraseArgs gdef))
                    Just (_, pos) => pure (NewTypeBy arity pos)
           Function _ def _ _ => pure (EraseArgs (countArgs def) (eraseArgs gdef))
           ExternDef arity => pure (Arity arity)
           ForeignDef arity _ => pure (Arity arity)
           _ => pure (Arity 0)
  where
    countArgs : forall vars . Term vars -> Nat
    countArgs (Bind _ _ (Lam{}) sc) = S (countArgs sc)
    countArgs _ = 0
numArgs _ tm = pure (Arity 0)

mkSub' : Nat -> (ns : SnocList Name) -> List Nat -> (ns' ** SubVars ns' ns)
mkSub' i _ [] = (_ ** SubRefl)
mkSub' i [<] ns = (_ ** SubRefl)
mkSub' (S i) (xs :< x) es
    = let (ns' ** p) = mkSub' i xs es in
          if i `elem` es
             then (ns' ** DropCons p)
             else (ns' :< x ** KeepCons p)
mkSub' _ _ _ = (_ ** SubRefl)

mkSub : (ns : SnocList Name) -> List Nat -> (ns' ** SubVars ns' ns)
mkSub ns = mkSub' (length ns) ns

weakenVar : Var ns -> Var (ns :< a)
weakenVar (MkVar p) = (MkVar (Later p))

etaExpand : {vars : _} ->
            Int -> Nat -> CExp vars -> List (Var vars) -> CExp vars
etaExpand i Z exp args = mkApp exp (map (mkLocal (getFC exp)) (reverse args))
  where
    mkLocal : FC -> (Var vars) -> CExp vars
    mkLocal fc (MkVar p) = CLocal fc p

    mkApp : CExp vars -> List (CExp vars) -> CExp vars
    mkApp tm [] = tm
    mkApp (CApp fc f args) args' = CApp fc f (args ++ args')
    mkApp (CCon fc n ci t args) args' = CCon fc n ci t (args ++ args')
    mkApp (CExtPrim fc p args) args' = CExtPrim fc p (args ++ args')
    mkApp tm args = CApp (getFC tm) tm args
etaExpand i (S k) exp args
    = CLam (getFC exp) (MN "eta" i)
             (etaExpand (i + 1) k (weaken exp)
                  (MkVar First :: map weakenVar args))

export
expandToArity : {vars : _} ->
                Nat -> CExp vars -> List (CExp vars) -> CExp vars
-- No point in applying to anything
expandToArity _ (CErased fc) _ = CErased fc
-- Overapplied; apply everything as single arguments
expandToArity Z f args = applyAll f args
  where
    applyAll : CExp vars -> List (CExp vars) -> CExp vars
    applyAll fn [] = fn
    applyAll fn (a :: args) = applyAll (CApp (getFC fn) fn [a]) args
expandToArity (S k) f (a :: args) = expandToArity k (addArg f a) args
  where
    addArg : CExp vars -> CExp vars -> CExp vars
    addArg (CApp fc fn args) a = CApp fc fn (args ++ [a])
    addArg (CCon fc n ci tag args) a = CCon fc n ci tag (args ++ [a])
    addArg (CExtPrim fc p args) a = CExtPrim fc p (args ++ [a])
    addArg f a = CApp (getFC f) f [a]
-- Underapplied, saturate with lambdas
expandToArity num fn [] = etaExpand 0 num fn []

applyNewType : {vars : _} ->
               Nat -> Nat -> CExp vars -> List (CExp vars) -> CExp vars
applyNewType arity pos fn args
    = let fn' = expandToArity arity fn args in
          keepArg fn' -- fn' might be lambdas, after eta expansion
  where
    keep : Nat -> List (CExp vs) -> CExp vs
    keep i [] = CErased (getFC fn) -- can't happen if all is well!
    keep i (x :: xs)
        = if i == pos
             then x
             else keep (1 + i) xs

    keepArg : CExp vs -> CExp vs
    keepArg (CLam fc x sc) = CLam fc x (keepArg sc)
    keepArg (CCon fc _ _ _ args) = keep 0 args
    keepArg tm = CErased (getFC fn)

dropFrom : List Nat -> Nat -> List (CExp vs) -> List (CExp vs)
dropFrom epos i [] = []
dropFrom epos i (x :: xs)
    = if i `elem` epos
         then dropFrom epos (1 + i) xs
         else x :: dropFrom epos (1 + i) xs

dropPos : List Nat -> CExp vs -> CExp vs
dropPos epos (CLam fc x sc) = CLam fc x (dropPos epos sc)
dropPos epos (CApp fc tm@(CApp _ _ _) args')
    = CApp fc (dropPos epos tm) args'
dropPos epos (CApp fc f args) = CApp fc f (dropFrom epos 0 args)
dropPos epos (CCon fc c ci a args) = CCon fc c ci a (dropFrom epos 0 args)
dropPos epos tm = tm

eraseConArgs : {vars : _} ->
               Nat -> List Nat -> CExp vars -> List (CExp vars) -> CExp vars
eraseConArgs arity epos fn args
    = let fn' = expandToArity arity fn args in
          if not (isNil epos)
             then dropPos epos fn' -- fn' might be lambdas, after eta expansion
             else fn'

mkDropSubst' : Nat -> List Nat ->
               (rest : SnocList Name) ->
               (vars : SnocList Name) ->
               (vars' ** SubVars (rest ++ vars') (rest ++ vars))
mkDropSubst' i es rest [<] = ([<] ** SubRefl)
mkDropSubst' (S i) es rest (xs :< x)
    = let (vs ** sub) = mkDropSubst' i es rest xs in
          if (S i) `elem` es
             then (vs ** DropCons sub)
             else (vs :< x ** KeepCons sub)
-- Next case can't happen if called with the right Nat from mkDropSubst
-- FIXME: rule it out with a type!
mkDropSubst' Z es rest (xs :< x)
    = let (vs ** sub) = mkDropSubst' Z es rest xs in
          (vs ** DropCons sub)

mkDropSubst : List Nat ->
              (rest : SnocList Name) ->
              (vars : SnocList Name) ->
              (vars' ** SubVars (rest ++ vars') (rest ++ vars))
mkDropSubst es rest xs = mkDropSubst' (length xs) es rest xs

-- Rewrite applications of Nat-like constructors and functions to more optimal
-- versions using Integer

-- None of these should be hard coded, but we'll do it this way until we
-- have a more general approach to optimising data types!
-- NOTE: Make sure that names mentioned here are listed in 'natHackNames' in
-- Common.idr, so that they get compiled, as they won't be spotted by the
-- usual calls to 'getRefs'.
data Magic : Type where
  MagicCCon : Name -> (arity : Nat) -> -- checks
              (FC -> forall vars. Vect arity (CExp vars) -> CExp vars) -> -- translation
              Magic
  MagicCRef : Name -> (arity : Nat) -> -- checks
              (FC -> FC -> forall vars. Vect arity (CExp vars) -> CExp vars) -> --translation
              Magic

magic : List Magic -> CExp vars -> CExp vars
magic ms (CLam fc x exp) = CLam fc x (magic ms exp)
magic ms e = go ms e where

  fire : Magic -> CExp vars -> Maybe (CExp vars)
  fire (MagicCCon n arity f) (CCon fc n' _ _ es)
    = do guard (n == n')
         map (f fc) (toVect arity es)
  fire (MagicCRef n arity f) (CApp fc (CRef fc' n') es)
    = do guard (n == n')
         map (f fc fc') (toVect arity es)
  fire _ _ = Nothing

  go : List Magic -> CExp vars -> CExp vars
  go [] e = e
  go (m :: ms) e = case fire m e of
    Nothing => go ms e
    Just e' => e'

%inline
magic__integerToNat : FC -> FC -> forall vars. Vect 1 (CExp vars) -> CExp vars
magic__integerToNat fc fc' [k]
  = CApp fc (CRef fc' (NS typesNS (UN $ Basic "prim__integerToNat"))) [k]

magic__natMinus : FC -> FC -> forall vars. Vect 2 (CExp vars) -> CExp vars
magic__natMinus fc fc' [m, n]
  = magic__integerToNat fc fc'
    [COp fc (Sub IntegerType) [m, n]]

-- We don't reuse natMinus here because we assume that unsuc will only be called
-- on S-headed numbers so we do not need the truncating integerToNat call!
magic__natUnsuc : FC -> FC -> forall vars. Vect 1 (CExp vars) -> CExp vars
magic__natUnsuc fc fc' [m]
  = COp fc (Sub IntegerType) [m, CPrimVal fc (BI 1)]

-- TODO: next release remove this and use %builtin pragma
natHack : List Magic
natHack =
    [ MagicCRef (NS typesNS (UN $ Basic "natToInteger")) 1 (\ _, _, [k] => k)
    , MagicCRef (NS typesNS (UN $ Basic "integerToNat")) 1 magic__integerToNat
    , MagicCRef (NS typesNS (UN $ Basic "plus")) 2
         (\ fc, fc', [m,n] => COp fc (Add IntegerType) [m, n])
    , MagicCRef (NS typesNS (UN $ Basic "mult")) 2
         (\ fc, fc', [m,n] => COp fc (Mul IntegerType) [m, n])
    , MagicCRef (NS typesNS (UN $ Basic "minus")) 2 magic__natMinus
    , MagicCRef (NS typesNS (UN $ Basic "equalNat")) 2
         (\ fc, fc', [m,n] => COp fc (EQ IntegerType) [m, n])
    , MagicCRef (NS typesNS (UN $ Basic "compareNat")) 2
         (\ fc, fc', [m,n] => CApp fc (CRef fc' (NS eqOrdNS (UN $ Basic "compareInteger"))) [m, n])
    ]

-- get all builtin transformations
builtinMagic : forall vars. CExp vars -> CExp vars
builtinMagic = magic natHack

data NextMN : Type where
newMN : {auto s : Ref NextMN Int} -> String -> Core Name
newMN base = do
    x <- get NextMN
    put NextMN $ x + 1
    pure $ MN base x

natBranch :  CConAlt vars -> Bool
natBranch (MkConAlt n ZERO _ _) = True
natBranch (MkConAlt n SUCC _ _) = True
natBranch _ = False

trySBranch : CExp vars -> CConAlt vars -> Maybe (CExp vars)
trySBranch n (MkConAlt nm SUCC _ (CArg arg (CRHS sc)))
    = Just (CLet (getFC n) arg True (magic__natUnsuc (getFC n) (getFC n) [n]) sc)
trySBranch _ _ = Nothing

tryZBranch : CConAlt vars -> Maybe (CExp vars)
tryZBranch (MkConAlt n ZERO _ (CRHS sc)) = Just sc
tryZBranch _ = Nothing

getSBranch : CExp vars -> List (CConAlt vars) -> Maybe (CExp vars)
getSBranch n [] = Nothing
getSBranch n (x :: xs) = trySBranch n x <|> getSBranch n xs

getZBranch : List (CConAlt vars) -> Maybe (CExp vars)
getZBranch [] = Nothing
getZBranch (x :: xs) = tryZBranch x <|> getZBranch xs

-- Rewrite case trees on Nat to be case trees on Integer
builtinNatTree : {auto s : Ref NextMN Int} -> CExp vars -> Core (CExp vars)
builtinNatTree (CConCase fc sc@(CLocal _ _) alts def)
   = pure $ if any natBranch alts
               then let defb = fromMaybe (CCrash fc "Nat case not covered") def
                        salt = maybe defb id (getSBranch sc alts)
                        zalt = maybe defb id (getZBranch alts) in
                        CConstCase fc sc [MkConstAlt (BI 0) zalt] (Just salt)
               else CConCase fc sc alts def
builtinNatTree (CConCase fc sc alts def)
    = do x <- newMN "succ"
         pure $ CLet fc x True sc
                !(builtinNatTree $ CConCase fc (CLocal fc First) (map weaken alts) (map weaken def))
builtinNatTree t = pure t

enumTag : Nat -> Int -> Constant
enumTag k i =
  if      k <= 0xff   then B8 (cast i)
  else if k <= 0xffff then B16 (cast i)
  else                     B32 (cast i)

enumTree : CExp vars -> CExp vars
enumTree (CConCase fc sc alts def)
   = let x = traverse toEnum alts
         Just alts' = x
              | Nothing => CConCase fc sc alts def in
         CConstCase fc sc alts' def
  where
    toEnum : CConAlt vars -> Maybe (CConstAlt vars)
    toEnum (MkConAlt nm (ENUM n) (Just tag) (CRHS sc))
        = pure $ MkConstAlt (enumTag n tag) sc
    toEnum _ = Nothing
enumTree t = t

-- remove pattern matches on unit
unitTree : {auto u : Ref NextMN Int} -> CExp vars -> Core (CExp vars)
unitTree exp@(CConCase fc sc alts def) = fromMaybe (pure exp)
    $ do let [MkConAlt _ UNIT _ (CRHS e)] = alts
             | _ => Nothing
         Just $ case sc of -- TODO: Check scrutinee has no effect, and skip let binding
                     CLocal _ _ => pure e
                     _ => pure $ CLet fc !(newMN "_unit") False sc (weaken e)
unitTree t = pure t

-- See if the constructor is a special constructor type, e.g a nil or cons
-- shaped thing.
dconFlag : {auto c : Ref Ctxt Defs} ->
           Name -> Core ConInfo
dconFlag n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Can't find " ++ show n))
         pure (ciFlags (definition def) (flags def))
  where
    ciFlags : Def -> List DefFlag -> ConInfo
    ciFlags def [] = case def of
      TCon{} => TYCON
      _ => DATACON
    ciFlags def (ConType ci :: xs) = ci
    ciFlags def (x :: xs) = ciFlags def xs

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
data ArgList : Nat -> SnocList Name -> Type where
     NoArgs : ArgList Z [<]
     ConsArg : (a : Name) -> ArgList k as -> ArgList (S k) (as :< a)

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** NoArgs)
mkArgList i (S k)
    = let (_ ** rec) = mkArgList (i + 1) k in
          (_ ** ConsArg (MN "arg" i) rec)

toCExpTm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto s : Ref NextMN Int} ->
           Name -> Term vars ->
           Core (CExp vars)
toCExp : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto s : Ref NextMN Int} ->
         Name -> Term vars ->
         Core (CExp vars)

conCases : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto s : Ref NextMN Int} ->
           Name -> List (CaseAlt vars) ->
           Core (List (CConAlt vars))
conCases n [] = pure []
conCases n (ConCase fc x tag sc :: ns)
    = do log "compiler.newtype.world" 50 "conCases-2 on \{show n} x: \{show x}, sc: \{show sc}"
         defs <- get Ctxt
         Just gdef <- lookupCtxtExact x (gamma defs)
              | Nothing => -- primitive type match
                   do xn <- getFullName x
                      pure $ MkConAlt xn TYCON Nothing !(toCExpScope 0 [] sc)
                               :: !(conCases n ns)
         let nt = case definition gdef of
                       DCon di _ arity => newTypeArg di
                       _ => Nothing
         case nt of
              Just pos => conCases n ns -- skip it
              _ => do xn <- getFullName x
                      let erased = eraseArgs gdef
                      log "compiler.newtype.world" 50 "conCases-2 on \{show n} erased: \{show erased}"
                      sc' <- toCExpScope 0 erased sc
                      ns' <- conCases n ns
                      log "compiler.newtype.world" 50 "conCases-2 on \{show n} ns': \{show ns'}"
                      if dcon (definition gdef)
                         then pure $ MkConAlt xn !(dconFlag xn) (Just tag) sc' :: ns'
                         else pure $ MkConAlt xn !(dconFlag xn) Nothing sc' :: ns'
  where
    dcon : Def -> Bool
    dcon (DCon _ _ _) = True
    dcon _ = False

    toCExpScope : {vars : _} -> Nat -> List Nat ->
                  CaseScope vars -> Core (CCaseScope vars)
    toCExpScope i es (RHS _ tm) = pure $ CRHS !(toCExp n tm)
    toCExpScope {vars} i es (Arg c x sc)
        = if i `elem` es
             then pure $ shrinkCScope (DropCons SubRefl) $
                          !(toCExpScope {vars = vars :< x} (S i) es sc)
             else pure $ CArg x !(toCExpScope {vars = vars :< x} (S i) es sc)
conCases n (_ :: ns) = conCases n ns

constCases : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref NextMN Int} ->
             Name -> List (CaseAlt vars) ->
             Core (List (CConstAlt vars))
constCases n [] = pure []
constCases n (ConstCase _ WorldVal sc :: ns)
    = constCases n ns
constCases n (ConstCase _ x sc :: ns)
    = pure $ MkConstAlt x !(toCExp n sc) ::
                  !(constCases n ns)
constCases n (_ :: ns) = constCases n ns

getDef : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto s : Ref NextMN Int} ->
         Name -> List (CaseAlt vars) ->
         Core (Maybe (CExp vars))
getDef n [] = pure Nothing
getDef n (DefaultCase fc sc :: ns)
    = pure $ Just !(toCExp n sc)
getDef n (ConstCase fc WorldVal sc :: ns)
    = pure $ Just !(toCExp n sc)
getDef n (_ :: ns) = getDef n ns

-- If there's a case which matches on a 'newtype', return the RHS
-- without matching.
-- Take some care if the newtype involves a WorldVal - in that case we
-- still need to let bind the scrutinee to ensure it's evaluated exactly
-- once.
getNewType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref NextMN Int} ->
             FC -> CExp vars ->
             Name -> List (CaseAlt vars) ->
             Core (Maybe (CExp vars))
getNewType fc scr n [] = pure Nothing
getNewType fc scr n (DefaultCase _ sc :: ns)
    = pure $ Nothing
getNewType fc scr n (ConCase _ x tag sc :: ns)
    = do defs <- get Ctxt
         Just (DCon di t a) <- lookupDefExact x (gamma defs)
              | _ => pure Nothing
         let Just (noworld, pos) = newTypeArg di
              | _ => pure Nothing
         if noworld
            then do log "compiler.newtype.world" 50 "Inlining case on \{show n} (no world)"
                    substScr 0 pos scr Lin sc
            else do log "compiler.newtype.world" 25 "Kept the scrutinee \{show n} \{show pos} sc \{show sc}, vars: \{show $ toList vars}, scr: \{show scr}"
                    substLetScr 0 pos scr Lin sc
  where
    -- no %World, so substitute diretly
    substScr : {args : _} ->
               Nat -> Nat -> CExp vars ->
               SubstCEnv args vars ->
               CaseScope (vars ++ args) ->
               Core (Maybe (CExp vars))
    substScr i pos x env (RHS _ tm)
        = do tm' <- toCExp n tm
             pure $ Just (substs env tm')
    substScr i pos x env (Arg c n sc)
        = if i == pos
             then substScr (S i) pos x (env :< x) sc
             else substScr (S i) pos x (env :< CErased fc) sc

    -- When we find the scrutinee, let bind it and substitute the name into
    -- the RHS, so the thing still gets evaluated if it's an action on %World
    substLetScr : {args : _} ->
               Nat -> Nat -> CExp vars ->
               SubstCEnv args (vars :< MN "eff" 0) ->
               CaseScope (vars ++ args) ->
               Core (Maybe (CExp vars))
    substLetScr i pos x env (RHS _ tm)
        = do tm' <- toCExp n tm
             let tm' = insertNames {outer = args} {inner = vars} {ns = [<MN "eff" 0]}
                            (mkSizeOf _) (mkSizeOf _) tm'
             let rettm = CLet fc (MN "eff" 0) False x
                       (substs env
                          (rewrite sym (appendAssociative vars [<MN "eff" 0] args)
                                     in tm'))
             pure $ Just rettm
    substLetScr i pos x env (Arg c n sc)
        = if i == pos
             then substLetScr (S i) pos x (env :< CLocal fc First) sc
             else substLetScr (S i) pos x (env :< CErased fc) sc

getNewType fc scr n (_ :: ns) = getNewType fc scr n ns

toCExpCase : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref NextMN Int} ->
             Name -> FC -> CExp vars -> List (CaseAlt vars) ->
             Core (CExp vars)
toCExpCase n fc x (DelayCase _ ty arg sc :: rest)
    = pure $
          CLet fc ty True (CErased fc) $
          CLet fc arg True (CForce fc LInf (weaken x)) $
               !(toCExp n sc)
toCExpCase n fc sc alts@(ConCase _ _ _ _ :: _)
    = do log "compiler.newtype.world" 50 "toCExpCase'-1 on \{show n} x: sc: \{show sc}, alts: \{show alts}"
         Nothing <- getNewType fc sc n alts
             | Just def => pure def
         defs <- get Ctxt
         cases <- conCases n alts
         def <- getDef n alts
         log "compiler.newtype.world" 50 "toCExpCase'-1 on \{show n} cases: \{show cases}, def: \{show def}"
         if isNil cases
            then pure (fromMaybe (CErased fc) def)
            else unitTree $ enumTree !(builtinNatTree $
                      CConCase fc sc cases def)
toCExpCase n fc sc alts@(ConstCase _ _ _ :: _)
    = do cases <- constCases n alts
         def <- getDef n alts
         if isNil cases
            then pure (fromMaybe (CErased fc) def)
            else pure $ CConstCase fc sc cases def
toCExpCase n fc _ alts@(DefaultCase _ tm :: _) = toCExp n tm
toCExpCase n fc sc []
      = pure $ CCrash fc $ "Missing case tree in " ++ show n

toCExpTm n (Local fc _ prf)
    = pure $ CLocal fc prf
toCExpTm n (Ref fc (DataCon tag arity) fn)
    = do -- get full name for readability, and %builtin Natural
         cn <- getFullName fn
         fl <- dconFlag cn
         case fl of
              (ENUM n) => pure $ CPrimVal fc (enumTag n tag)
              ZERO => pure $ CPrimVal fc (BI 0)
              SUCC => do x <- newMN "succ"
                         pure $ CLam fc x $ COp fc (Add IntegerType) [CPrimVal fc (BI 1), CLocal fc First]
              _ => pure $ CCon fc cn fl (Just tag) []
toCExpTm n (Ref fc (TyCon arity) fn)
    = pure $ CCon fc fn TYCON Nothing []
toCExpTm n (Ref fc _ fn)
    = do full <- getFullName fn
             -- ^ For readability of output code, and the Nat hack,
         pure $ CApp fc (CRef fc full) []
toCExpTm n (Meta fc mn i args)
    = pure $ CApp fc (CRef fc mn) !(traverse (toCExp n) (map snd args))
toCExpTm n (Bind fc x (Lam _ _ _ _) sc)
    = pure $ CLam fc x !(toCExp n sc)
toCExpTm n (Bind fc x (Let _ rig val _) sc)
    = do sc' <- toCExp n sc
         pure $ branchZero (shrinkCExp (DropCons SubRefl) sc')
                        (CLet fc x True !(toCExp n val) sc')
                        rig
toCExpTm n (Bind fc x (Pi _ c e ty) sc)
    = pure $ CCon fc (UN (Basic "->")) TYCON Nothing
                     [ !(toCExp n ty)
                     , CLam fc x !(toCExp n sc)]
toCExpTm n (Bind fc x b tm) = pure $ CErased fc
-- We'd expect this to have been dealt with in toCExp, but for completeness...
toCExpTm n (App fc tm _ arg)
    = pure $ CApp fc !(toCExp n tm) [!(toCExp n arg)]
-- This shouldn't be in terms any more, but here for completeness
toCExpTm n (As _ _ _ p) = toCExpTm n p
-- TODO: Either make sure 'Delayed' is always Rig0, or add to typecase
toCExpTm n (Case fc _ _ sc _ alts)
    = toCExpCase n fc !(toCExp n sc) alts
toCExpTm n (TDelayed fc _ _) = pure $ CErased fc
toCExpTm n (TDelay fc lr _ arg)
    = pure (CDelay fc lr !(toCExp n arg))
toCExpTm n (TForce fc lr arg)
    = pure (CForce fc lr !(toCExp n arg))
toCExpTm n (PrimVal fc $ PrT c) = pure $ CCon fc (UN $ Basic $ show c) TYCON Nothing [] -- Primitive type constant
toCExpTm n (PrimVal fc c) = pure $ CPrimVal fc c -- Non-type constant
toCExpTm n (PrimOp {arity} fc fn args)
    = pure $ COp fc fn !(traverseVect (toCExp n) args)
toCExpTm n (Erased fc _) = pure $ CErased fc
toCExpTm n (Unmatched fc str) = pure $ CCrash fc str
toCExpTm n (TType fc _) = pure $ CCon fc (UN (Basic "Type")) TYCON Nothing []

toCExp n tm
    = case getFnArgs tm of
           (f, args) =>
              do args' <- traverse (toCExp n) args
                 defs <- get Ctxt
                 f' <- toCExpTm n f
                 Arity a <- numArgs defs f
                    | NewTypeBy arity pos =>
                          do let res = applyNewType arity pos f' args'
                             pure $ builtinMagic res
                    | EraseArgs arity epos =>
                          do let res = eraseConArgs arity epos f' args'
                             pure $ builtinMagic res
                 let res = expandToArity a f' args'
                 pure $ builtinMagic res

data NArgs : Type where
     User : Name -> List (Glued [<]) -> NArgs
     Struct : String -> List (String, Glued [<]) -> NArgs
     NUnit : NArgs
     NPtr : NArgs
     NGCPtr : NArgs
     NBuffer : NArgs
     NForeignObj : NArgs
     NIORes : Glued [<] -> NArgs

getPArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> Glued [<] -> Core (String, Glued [<])
getPArgs defs cl
    = do VDCon fc _ _ _ args <- expand cl
             | nf => throw (GenericMsg (getLoc nf) "Badly formed struct type")
         case !(traverseSnocList value args) of
              (_ :< n :< tydesc) =>
                  do VPrimVal _ (Str n') <- expand n
                         | nf => throw (GenericMsg (getLoc nf) "Unknown field name")
                     pure (n', tydesc)
              _ => throw (GenericMsg fc "Badly formed struct type")

getFieldArgs : {auto c : Ref Ctxt Defs} ->
               Defs -> Glued [<] -> Core (List (String, Glued [<]))
getFieldArgs defs cl
    = do VDCon fc _ _ _ args <- expand cl
             | nf => throw (GenericMsg (getLoc nf) "Badly formed struct type")
         case !(traverseSnocList value args) of
              -- cons
              [< _, t, rest] =>
                  do rest' <- getFieldArgs defs rest
                     (n, ty) <- getPArgs defs t
                     pure ((n, ty) :: rest')
              -- nil
              _ => pure []

getNArgs : {auto c : Ref Ctxt Defs} ->
           Defs -> Name -> List (Glued [<]) -> Core NArgs
getNArgs defs (NS _ (UN $ Basic "IORes")) [arg] = pure $ NIORes arg
getNArgs defs (NS _ (UN $ Basic "Ptr")) [arg] = pure NPtr
getNArgs defs (NS _ (UN $ Basic "AnyPtr")) [] = pure NPtr
getNArgs defs (NS _ (UN $ Basic "GCPtr")) [arg] = pure NGCPtr
getNArgs defs (NS _ (UN $ Basic "GCAnyPtr")) [] = pure NGCPtr
getNArgs defs (NS _ (UN $ Basic "Buffer")) [] = pure NBuffer
getNArgs defs (NS _ (UN $ Basic "ForeignObj")) [] = pure NForeignObj
getNArgs defs (NS _ (UN $ Basic "Unit")) [] = pure NUnit
getNArgs defs (NS _ (UN $ Basic "Struct")) [n, args]
    = do VPrimVal _ (Str n') <- expand n
             | nf => throw (GenericMsg (getLoc nf) "Unknown name for struct")
         pure (Struct n' !(getFieldArgs defs args))
getNArgs defs n args = pure $ User n args

nfToCFType : {auto c : Ref Ctxt Defs} ->
             FC -> (inStruct : Bool) -> NF [<] -> Core CFType
nfToCFType _ _ (VPrimVal _ $ PrT IntType) = pure CFInt
nfToCFType _ _ (VPrimVal _ $ PrT IntegerType) = pure CFInteger
nfToCFType _ _ (VPrimVal _ $ PrT Bits8Type) = pure CFUnsigned8
nfToCFType _ _ (VPrimVal _ $ PrT Bits16Type) = pure CFUnsigned16
nfToCFType _ _ (VPrimVal _ $ PrT Bits32Type) = pure CFUnsigned32
nfToCFType _ _ (VPrimVal _ $ PrT Bits64Type) = pure CFUnsigned64
nfToCFType _ _ (VPrimVal _ $ PrT Int8Type) = pure CFInt8
nfToCFType _ _ (VPrimVal _ $ PrT Int16Type) = pure CFInt16
nfToCFType _ _ (VPrimVal _ $ PrT Int32Type) = pure CFInt32
nfToCFType _ _ (VPrimVal _ $ PrT Int64Type) = pure CFInt64
nfToCFType _ False (VPrimVal _ $ PrT StringType) = pure CFString
nfToCFType fc True (VPrimVal _ $ PrT StringType)
    = throw (GenericMsg fc "String not allowed in a foreign struct")
nfToCFType _ _ (VPrimVal _ $ PrT DoubleType) = pure CFDouble
nfToCFType _ _ (VPrimVal _ $ PrT CharType) = pure CFChar
nfToCFType _ _ (VPrimVal _ $ PrT WorldType) = pure CFWorld
nfToCFType _ False (VBind fc _ (Pi _ _ _ ty) sc)
    = do defs <- get Ctxt
         sty <- nfToCFType fc False !(expand ty)
         sc' <- expand !(sc (pure (VErased fc Placeholder)))
         tty <- nfToCFType fc False sc'
         pure (CFFun sty tty)
nfToCFType _ True (VBind fc _ _ _)
    = throw (GenericMsg fc "Function types not allowed in a foreign struct")
nfToCFType _ s (VTCon fc n_in _ args)
    = do defs <- get Ctxt
         n <- toFullNames n_in
         case !(getNArgs defs n $ cast !(traverseSnocList value args)) of
              User un uargs =>
                do nargs <- traverse expand uargs
                   cargs <- traverse (nfToCFType fc s) nargs
                   pure (CFUser n cargs)
              Struct n fs =>
                do fs' <- traverse
                             (\ (n, ty) =>
                                    do tynf <- expand ty
                                       tycf <- nfToCFType fc True tynf
                                       pure (n, tycf)) fs
                   pure (CFStruct n fs')
              NUnit => pure CFUnit
              NPtr => pure CFPtr
              NGCPtr => pure CFGCPtr
              NBuffer => pure CFBuffer
              NForeignObj => pure CFForeignObj
              NIORes uarg =>
                do narg <- expand uarg
                   carg <- nfToCFType fc s narg
                   pure (CFIORes carg)
nfToCFType _ s (VType _ _)
    = pure (CFUser (UN (Basic "Type")) [])
nfToCFType _ s (VErased _ _)
    = pure (CFUser (UN (Basic "__")) [])
nfToCFType fc s t
    = do defs <- get Ctxt
         ty <- quote [<] t
         throw (GenericMsg (getLoc t)
                       ("Can't marshal type for foreign call " ++
                                      show !(toFullNames ty)))

getCFTypes : {auto c : Ref Ctxt Defs} ->
             List CFType -> NF [<] ->
             Core (List CFType, CFType)
getCFTypes args (VBind fc _ (Pi _ _ _ ty) sc)
    = do defs <- get Ctxt
         aty <- nfToCFType fc False !(expand ty)
         sc' <- expand !(sc (pure (VErased fc Placeholder)))
         getCFTypes (aty :: args) sc'
getCFTypes args t
    = pure (reverse args, !(nfToCFType (getLoc t) False t))

lamRHSenv : Int -> FC -> (ns : SnocList Name) -> SubstCEnv ns [<]
lamRHSenv i fc [<] = [<]
lamRHSenv i fc (ns :< n)
    = lamRHSenv (i + 1) fc ns :< CRef fc (MN "x" i)

mkBounds : (xs : _) -> Bounds xs
mkBounds [<] = None
mkBounds (xs :< x) = Add x x (mkBounds xs)

getNewArgs : {done : _} ->
             SubstCEnv done args -> SnocList Name
getNewArgs [<] = [<]
getNewArgs (xs :< CRef _ n) = getNewArgs xs :< n
getNewArgs {done = xs :< x} (sub :< _) = getNewArgs sub :< x

-- If a name is declared in one module and defined in another,
-- we have to assume arity 0 for incremental compilation because
-- we have no idea how it's defined, and when we made calls to the
-- function, they had arity 0.
lamRHS : (ns : SnocList Name) -> CExp ns -> CExp [<]
lamRHS ns tm
    = let env = lamRHSenv 0 (getFC tm) ns
          tmExp = substs env (rewrite appendLinLeftNeutral ns in tm)
          newArgs = reverse $ getNewArgs env
          bounds = mkBounds newArgs
          expLocs = mkLocals zero {vars = [<]} bounds tmExp in
          lamBind (getFC tm) _ expLocs
  where
    lamBind : FC -> (ns : SnocList Name) -> CExp ns -> CExp [<]
    lamBind fc [<] tm = tm
    lamBind fc (ns :< n) tm = lamBind fc ns (CLam fc n tm)

export
mergeLambdas : (args : SnocList Name) -> CExp args -> (args' ** CExp args')
mergeLambdas args (CLam fc x sc)
    = mergeLambdas (args :< x) sc
mergeLambdas args exp = (args ** exp)

toCDef : {auto c : Ref Ctxt Defs} ->
         Name -> ClosedTerm -> List Nat -> Def ->
         Core CDef
toCDef n ty _ None
    = pure $ MkError $ CCrash emptyFC ("Encountered undefined name " ++ show !(getFullName n))
toCDef n ty erased (Function fi _ tree _)
    = do log "compiler.newtype.world" 25 "toCDef PMDef ty: \{show ty}, n: \{show n}, erased: \{show erased}, tree: \{show tree}"
         s <- newRef NextMN 0
         t <- toCExp n tree
         log "compiler.newtype.world" 25 "toCDef PMDef t: \{show t}"
         let (args ** comptree) = mergeLambdas [<] t
         let (args' ** p) = mkSub args erased
         log "compiler.newtype.world" 25 "toCDef PMDef comptree \{show comptree}, is_ext: \{show $ (externalDecl fi)}"
         pure $ toLam (externalDecl fi) $ if isNil erased
            then MkFun args comptree
            else MkFun args' (shrinkCExp p comptree)
  where
    toLam : Bool -> CDef -> CDef
    toLam True (MkFun args rhs) = MkFun [<] (lamRHS args rhs)
    toLam _ d = d
toCDef n ty _ (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          -- Reverse the args since we build them in the wrong order (most
          -- recently bound lambda is last argument to primitive)
          pure $ MkFun _ (CExtPrim emptyFC !(getFullName n)
                             (reverse (map toArgExp (getVars args))))
  where
    toArgExp : (Var ns) -> CExp ns
    toArgExp (MkVar p) = CLocal emptyFC p

    getVars : ArgList k ns -> List (Var ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = MkVar First :: map weakenVar (getVars rest)
toCDef n ty _ (ForeignDef arity cs)
    = do defs <- get Ctxt
         (atys, retty) <- getCFTypes [] !(expand !(nf [<] ty))
         pure $ MkForeign cs atys retty
toCDef n _ _ (DCon pos tag arity)
    = do let nt = snd <$> (newTypeArg pos)
         defs <- get Ctxt
         args <- numArgs {vars = [<]} defs (Ref EmptyFC (DataCon tag arity) n)
         let arity' = case args of
                 NewTypeBy ar _ => ar
                 EraseArgs ar erased => ar `minus` length erased
                 Arity ar => ar
         pure $ MkCon (Just tag) arity' nt
toCDef n _ _ (TCon ti arity)
    = pure $ MkCon Nothing arity Nothing
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef n ty _ (Hole _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered unimplemented hole " ++
                                       show !(getFullName n))
toCDef n ty _ (Guess _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered constrained hole " ++
                                       show !(getFullName n))
toCDef n ty _ (BySearch _ _ _)
    = pure $ MkError $ CCrash emptyFC ("Encountered incomplete proof search " ++
                                       show !(getFullName n))
toCDef n ty _ def
    = pure $ MkError $ CCrash emptyFC ("Encountered uncompilable name " ++
                                       show (!(getFullName n), def))

export
compileExp : {auto c : Ref Ctxt Defs} ->
             ClosedTerm -> Core (CExp [<])
compileExp tm
    = do s <- newRef NextMN 0
         exp <- toCExp (UN $ Basic "main") tm
         pure exp

||| Given a name, look up an expression, and compile it to a CExp in the environment
export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core ()
compileDef n
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
         -- If we're incremental, and the name has no definition yet, it
         -- might end up defined in another module, so leave it, but warn
         if noDefYet (definition gdef) (incrementalCGs !getSession)
           -- This won't be accurate if we have names declared in one module
           -- and defined elsewhere. It's tricky to do the complete check that
           -- we do for whole program compilation, though, since that involves
           -- traversing everything from the main expression.
           -- For now, consider it an incentive not to have cycles :).
            then recordWarning (GenericWarn ("Compiling hole " ++ show n))
            else do log "compiler.newtype.world" 25 "compileDef name \{show n}, type gdef: \{show $ type gdef}"
                    ce <- logDepth $ toCDef n (type gdef) (eraseArgs gdef)
                           !(toFullNames (definition gdef))
                    setCompiled n ce
  where
    noDefYet : Def -> List CG -> Bool
    noDefYet None (_ :: _) = True
    noDefYet _ _ = False
