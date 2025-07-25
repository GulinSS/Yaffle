module TTImp.Reflect

import Core.Context
import Core.Env
import Core.Evaluate
import Core.Reflect
import Core.TT

import TTImp.TTImp

import Libraries.Data.WithDefault

%default covering

export
Reify BindMode where
  reify defs val@(VDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
             (UN (Basic "PI"), [c])
                 => do c' <- reify defs !(expand c)
                       pure (PI c')
             (UN (Basic "PATTERN"), _) => pure PATTERN
             (UN (Basic "COVERAGE"), _) => pure COVERAGE
             (UN (Basic "NONE"), _) => pure NONE
             _ => cantReify val "BindMode"
  reify deva val = cantReify val "BindMode"

export
Reflect BindMode where
  reflect fc defs lhs env (PI c)
      = do c' <- reflect fc defs lhs env c
           appConTop fc defs (reflectionttimp "PI") [c']
  reflect fc defs lhs env PATTERN
      = getCon fc defs (reflectionttimp "PATTERN")
  reflect fc defs lhs env COVERAGE
      = getCon fc defs (reflectionttimp "COVERAGE")
  reflect fc defs lhs env NONE
      = getCon fc defs (reflectionttimp "NONE")

export
Reify UseSide where
  reify defs val@(VDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "UseLeft"), _) => pure UseLeft
             (UN (Basic "UseRight"), _) => pure UseRight
             _ => cantReify val "UseSide"
  reify defs val = cantReify val "UseSide"

export
Reflect UseSide where
  reflect fc defs lhs env UseLeft
      = getCon fc defs (reflectionttimp "UseLeft")
  reflect fc defs lhs env UseRight
      = getCon fc defs (reflectionttimp "UseRight")

export
Reify DotReason where
  reify defs val@(VDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "NonLinearVar"), _) => pure NonLinearVar
             (UN (Basic "VarApplied"), _) => pure VarApplied
             (UN (Basic "NotConstructor"), _) => pure NotConstructor
             (UN (Basic "ErasedArg"), _) => pure ErasedArg
             (UN (Basic "UserDotted"), _) => pure UserDotted
             (UN (Basic "UnknownDot"), _) => pure UnknownDot
             (UN (Basic "UnderAppliedCon"), _) => pure UnderAppliedCon
             _ => cantReify val "DotReason"
  reify defs val = cantReify val "DotReason"

export
Reflect DotReason where
  reflect fc defs lhs env NonLinearVar
      = getCon fc defs (reflectionttimp "NonLinearVar")
  reflect fc defs lhs env VarApplied
      = getCon fc defs (reflectionttimp "VarApplied")
  reflect fc defs lhs env NotConstructor
      = getCon fc defs (reflectionttimp "NotConstructor")
  reflect fc defs lhs env ErasedArg
      = getCon fc defs (reflectionttimp "ErasedArg")
  reflect fc defs lhs env UserDotted
      = getCon fc defs (reflectionttimp "UserDotted")
  reflect fc defs lhs env UnknownDot
      = getCon fc defs (reflectionttimp "UnknownDot")
  reflect fc defs lhs env UnderAppliedCon
      = getCon fc defs (reflectionttimp "UnderAppliedCon")


mutual
  export
  Reify RawImp where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "IVar"), [fc, n])
                    => do fc' <- reify defs !(expand fc)
                          n' <- reify defs !(expand n)
                          pure (IVar fc' n')
               (UN (Basic "IPi"), [fc, c, p, mn, aty, rty])
                    => do fc' <- reify defs !(expand fc)
                          c' <- reify defs !(expand c)
                          p' <- reify defs !(expand p)
                          mn' <- reify defs !(expand mn)
                          aty' <- reify defs !(expand aty)
                          rty' <- reify defs !(expand rty)
                          pure (IPi fc' c' p' mn' aty' rty')
               (UN (Basic "ILam"), [fc, c, p, mn, aty, lty])
                    => do fc' <- reify defs !(expand fc)
                          c' <- reify defs !(expand c)
                          p' <- reify defs !(expand p)
                          mn' <- reify defs !(expand mn)
                          aty' <- reify defs !(expand aty)
                          lty' <- reify defs !(expand lty)
                          pure (ILam fc' c' p' mn' aty' lty')
               (UN (Basic "ILet"), [fc, lhsFC, c, n, ty, val, sc])
                    => do fc' <- reify defs !(expand fc)
                          lhsFC' <- reify defs !(expand lhsFC)
                          c' <- reify defs !(expand c)
                          n' <- reify defs !(expand n)
                          ty' <- reify defs !(expand ty)
                          val' <- reify defs !(expand val)
                          sc' <- reify defs !(expand sc)
                          pure (ILet fc' lhsFC' c' n' ty' val' sc')
               (UN (Basic "ICase"), [fc, opts, sc, ty, cs])
                    => do fc' <- reify defs !(expand fc)
                          opts' <- reify defs !(expand opts)
                          sc' <- reify defs !(expand sc)
                          ty' <- reify defs !(expand ty)
                          cs' <- reify defs !(expand cs)
                          pure (ICase fc' opts' sc' ty' cs')
               (UN (Basic "ILocal"), [fc, ds, sc])
                    => do fc' <- reify defs !(expand fc)
                          ds' <- reify defs !(expand ds)
                          sc' <- reify defs !(expand sc)
                          pure (ILocal fc' ds' sc')
               (UN (Basic "IUpdate"), [fc, ds, sc])
                    => do fc' <- reify defs !(expand fc)
                          ds' <- reify defs !(expand ds)
                          sc' <- reify defs !(expand sc)
                          pure (IUpdate fc' ds' sc')
               (UN (Basic "IApp"), [fc, f, a])
                    => do fc' <- reify defs !(expand fc)
                          f' <- reify defs !(expand f)
                          a' <- reify defs !(expand a)
                          pure (IApp fc' f' a')
               (UN (Basic "INamedApp"), [fc, f, m, a])
                    => do fc' <- reify defs !(expand fc)
                          f' <- reify defs !(expand f)
                          m' <- reify defs !(expand m)
                          a' <- reify defs !(expand a)
                          pure (INamedApp fc' f' m' a')
               (UN (Basic "IAutoApp"), [fc, f, a])
                    => do fc' <- reify defs !(expand fc)
                          f' <- reify defs !(expand f)
                          a' <- reify defs !(expand a)
                          pure (IAutoApp fc' f' a')
               (UN (Basic "IWithApp"), [fc, f, a])
                    => do fc' <- reify defs !(expand fc)
                          f' <- reify defs !(expand f)
                          a' <- reify defs !(expand a)
                          pure (IWithApp fc' f' a')
               (UN (Basic "ISearch"), [fc, d])
                    => do fc' <- reify defs !(expand fc)
                          d' <- reify defs !(expand d)
                          pure (ISearch fc' d')
               (UN (Basic "IAlternative"), [fc, t, as])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          as' <- reify defs !(expand as)
                          pure (IAlternative fc' t' as')
               (UN (Basic "IRewrite"), [fc, t, sc])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          sc' <- reify defs !(expand sc)
                          pure (IRewrite fc' t' sc')
               (UN (Basic "IBindHere"), [fc, t, sc])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          sc' <- reify defs !(expand sc)
                          pure (IBindHere fc' t' sc')
               (UN (Basic "IBindVar"), [fc, n])
                    => do fc' <- reify defs !(expand fc)
                          n' <- reify defs !(expand n)
                          pure (IBindVar fc' n')
               (UN (Basic "IAs"), [fc, nameFC, s, n, t])
                    => do fc' <- reify defs !(expand fc)
                          nameFC' <- reify defs !(expand nameFC)
                          s' <- reify defs !(expand s)
                          n' <- reify defs !(expand n)
                          t' <- reify defs !(expand t)
                          pure (IAs fc' nameFC' s' n' t')
               (UN (Basic "IMustUnify"), [fc, r, t])
                    => do fc' <- reify defs !(expand fc)
                          r' <- reify defs !(expand r)
                          t' <- reify defs !(expand t)
                          pure (IMustUnify fc' r' t')
               (UN (Basic "IDelayed"), [fc, r, t])
                    => do fc' <- reify defs !(expand fc)
                          r' <- reify defs !(expand r)
                          t' <- reify defs !(expand t)
                          pure (IDelayed fc' r' t')
               (UN (Basic "IDelay"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IDelay fc' t')
               (UN (Basic "IForce"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IForce fc' t')
               (UN (Basic "IQuote"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IQuote fc' t')
               (UN (Basic "IQuoteName"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IQuoteName fc' t')
               (UN (Basic "IQuoteDecl"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IQuoteDecl fc' t')
               (UN (Basic "IUnquote"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IUnquote fc' t')
               (UN (Basic "IPrimVal"), [fc, t])
                    => do fc' <- reify defs !(expand fc)
                          t' <- reify defs !(expand t)
                          pure (IPrimVal fc' t')
               (UN (Basic "IType"), [fc])
                    => do fc' <- reify defs !(expand fc)
                          pure (IType fc')
               (UN (Basic "IHole"), [fc, n])
                    => do fc' <- reify defs !(expand fc)
                          n' <- reify defs !(expand n)
                          pure (IHole fc' n')
               (UN (Basic "Implicit"), [fc, n])
                    => do fc' <- reify defs !(expand fc)
                          n' <- reify defs !(expand n)
                          pure (Implicit fc' n')
               (UN (Basic "IWithUnambigNames"), [fc, ns, t])
                    => do fc' <- reify defs !(expand fc)
                          ns' <- reify defs !(expand ns)
                          t' <- reify defs !(expand t)
                          pure (IWithUnambigNames fc' ns' t')
               _ => cantReify val "VDCon"
    reify defs val = cantReify val "VDCon"

  export
  Reify IFieldUpdate where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "ISetField"), [x, y])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          pure (ISetField x' y')
               (UN (Basic "ISetFieldApp"), [x, y])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          pure (ISetFieldApp x' y')
               _ => cantReify val "IFieldUpdate"
    reify defs val = cantReify val "IFieldUpdate"

  export
  Reify AltType where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "FirstSuccess"), _)
                    => pure FirstSuccess
               (UN (Basic "Unique"), _)
                    => pure Unique
               (UN (Basic "UniqueDefault"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (UniqueDefault x')
               _ => cantReify val "AltType"
    reify defs val = cantReify val "AltType"

  export
  Reify FnOpt where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "Unsafe"), _) => pure Unsafe
               (UN (Basic "Inline"), _) => pure Inline
               (UN (Basic "NoInline"), _) => pure NoInline
               (UN (Basic "Deprecate"), _) => pure Deprecate
               (UN (Basic "TCInline"), _) => pure TCInline
               (UN (Basic "Hint"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (Hint x')
               (UN (Basic "GlobalHint"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (GlobalHint x')
               (UN (Basic "ExternFn"), _) => pure ExternFn
               (UN (Basic "ForeignFn"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (ForeignFn x')
               (UN (Basic "ForeignExport"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (ForeignExport x')
               (UN (Basic "Invertible"), _) => pure Invertible
               (UN (Basic "Totality"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (Totality x')
               (UN (Basic "Macro"), _) => pure Macro
               (UN (Basic "SpecArgs"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (SpecArgs x')
               _ => cantReify val "FnOpt"
    reify defs val = cantReify val "FnOpt"

  export
  Reify ImpTy where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "MkTy"), [w, x, y, z])
                    => do w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (MkImpTy w' x' y' z')
               _ => cantReify val "ITy"
    reify defs val = cantReify val "ITy"

  export
  Reify DataOpt where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "SearchBy"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (SearchBy x')
               (UN (Basic "NoHints"), _) => pure NoHints
               (UN (Basic "UniqueSearch"), _) => pure UniqueSearch
               (UN (Basic "External"), _) => pure External
               (UN (Basic "NoNewtype"), _) => pure NoNewtype
               _ => cantReify val "DataOpt"
    reify defs val = cantReify val "DataOpt"

  export
  Reify ImpData where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "MkData"), [v,w,x,y,z])
                    => do v' <- reify defs !(expand v)
                          w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (MkImpData v' w' x' y' z')
               (UN (Basic "MkLater"), [x,y,z])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (MkImpLater x' y' z')
               _ => cantReify val "Data"
    reify defs val = cantReify val "Data"

  export
  Reify IField where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "MkIField"), [v,w,x,y,z])
                    => do v' <- reify defs !(expand v)
                          w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (MkIField v' w' x' y' z')
               _ => cantReify val "IField"
    reify defs val = cantReify val "IField"

  export
  Reify ImpRecord where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "MkRecord"), [v,w,x,y,z,a])
                    => do v' <- reify defs !(expand v)
                          w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          a' <- reify defs !(expand a)
                          pure (MkImpRecord v' w' x' y' z' a')
               _ => cantReify val "Record"
    reify defs val = cantReify val "Record"

  export
  Reify WithFlag where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "Syntactic"), [])
                    => pure Syntactic
               _ => cantReify val "WithFlag"
    reify defs val = cantReify val "WithFlag"

  export
  Reify ImpClause where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "PatClause"), [x,y,z])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (PatClause x' y' z')
               (UN (Basic "WithClause"), [u,v,w,x,y,z,a])
                    => do u' <- reify defs !(expand u)
                          v' <- reify defs !(expand v)
                          w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          a' <- reify defs !(expand a)
                          pure (WithClause u' v' w' x' y' z' a')
               (UN (Basic "ImpossibleClause"), [x,y])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          pure (ImpossibleClause x' y')
               _ => cantReify val "Clause"
    reify defs val = cantReify val "Clause"

  export
  Reify ImpDecl where
    reify defs val@(VDCon _ n _ _ args)
        = case (dropAllNS !(full (gamma defs) n), !(spine args)) of
               (UN (Basic "IClaim"), [v,w,x,y,z])
                    => do v' <- reify defs !(expand v)
                          w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (IClaim v' w' x' y' z')
               (UN (Basic "IData"), [x,y,z,w])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          w' <- reify defs !(expand w)
                          pure (IData x' y' z' w')
               (UN (Basic "IDef"), [x,y,z])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (IDef x' y' z')
               (UN (Basic "IParameters"), [x,y,z])
                    => do x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (IParameters x' y' z')
               (UN (Basic "IRecord"), [w,x,y,z,u])
                    => do w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          u' <- reify defs !(expand u)
                          pure (IRecord w' x' y' z' u')
               (UN (Basic "IFail"), [w,x,y])
                    => do w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          pure (IFail w' x' y')
               (UN (Basic "INamespace"), [w,x,y])
                    => do w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          pure (INamespace w' x' y')
               (UN (Basic "ITransform"), [w,x,y,z])
                    => do w' <- reify defs !(expand w)
                          x' <- reify defs !(expand x)
                          y' <- reify defs !(expand y)
                          z' <- reify defs !(expand z)
                          pure (ITransform w' x' y' z')
               (UN (Basic "ILog"), [x])
                    => do x' <- reify defs !(expand x)
                          pure (ILog x')
               _ => cantReify val "Decl"
    reify defs val = cantReify val "Decl"

mutual
  export
  Reflect RawImp where
    reflect fc defs lhs env (IVar tfc n)
        = do fc' <- reflect fc defs lhs env tfc
             n' <- reflect fc defs lhs env n
             appConTop fc defs (reflectionttimp "IVar") [fc', n']
    reflect fc defs lhs env (IPi tfc c p mn aty rty)
        = do fc' <- reflect fc defs lhs env tfc
             c' <- reflect fc defs lhs env c
             p' <- reflect fc defs lhs env p
             mn' <- reflect fc defs lhs env mn
             aty' <- reflect fc defs lhs env aty
             rty' <- reflect fc defs lhs env rty
             appConTop fc defs (reflectionttimp "IPi") [fc', c', p', mn', aty', rty']
    reflect fc defs lhs env (ILam tfc c p mn aty rty)
        = do fc' <- reflect fc defs lhs env tfc
             c' <- reflect fc defs lhs env c
             p' <- reflect fc defs lhs env p
             mn' <- reflect fc defs lhs env mn
             aty' <- reflect fc defs lhs env aty
             rty' <- reflect fc defs lhs env rty
             appConTop fc defs (reflectionttimp "ILam") [fc', c', p', mn', aty', rty']
    reflect fc defs lhs env (ILet tfc lhsFC c n aty aval sc)
        = do fc' <- reflect fc defs lhs env tfc
             lhsFC' <- reflect fc defs lhs env lhsFC
             c' <- reflect fc defs lhs env c
             n' <- reflect fc defs lhs env n
             aty' <- reflect fc defs lhs env aty
             aval' <- reflect fc defs lhs env aval
             sc' <- reflect fc defs lhs env sc
             appConTop fc defs (reflectionttimp "ILet") [fc', lhsFC', c', n', aty', aval', sc']
    reflect fc defs lhs env (ICase tfc opts sc ty cs)
        = do fc' <- reflect fc defs lhs env tfc
             opts' <- reflect fc defs lhs env opts
             sc' <- reflect fc defs lhs env sc
             ty' <- reflect fc defs lhs env ty
             cs' <- reflect fc defs lhs env cs
             appConTop fc defs (reflectionttimp "ICase") [fc', opts', sc', ty', cs']
    reflect fc defs lhs env (ILocal tfc ds sc)
        = do fc' <- reflect fc defs lhs env tfc
             ds' <- reflect fc defs lhs env ds
             sc' <- reflect fc defs lhs env sc
             appConTop fc defs (reflectionttimp "ILocal") [fc', ds', sc']
    reflect fc defs lhs env (ICaseLocal tfc u i args t)
        = reflect fc defs lhs env t -- shouldn't see this anyway...
    reflect fc defs lhs env (IUpdate tfc ds sc)
        = do fc' <- reflect fc defs lhs env tfc
             ds' <- reflect fc defs lhs env ds
             sc' <- reflect fc defs lhs env sc
             appConTop fc defs (reflectionttimp "IUpdate") [fc', ds', sc']
    reflect fc defs lhs env (IApp tfc f a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             a' <- reflect fc defs lhs env a
             appConTop fc defs (reflectionttimp "IApp") [fc', f', a']
    reflect fc defs lhs env (IAutoApp tfc f a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             a' <- reflect fc defs lhs env a
             appConTop fc defs (reflectionttimp "IAutoApp") [fc', f', a']
    reflect fc defs lhs env (INamedApp tfc f m a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             m' <- reflect fc defs lhs env m
             a' <- reflect fc defs lhs env a
             appConTop fc defs (reflectionttimp "INamedApp") [fc', f', m', a']
    reflect fc defs lhs env (IWithApp tfc f a)
        = do fc' <- reflect fc defs lhs env tfc
             f' <- reflect fc defs lhs env f
             a' <- reflect fc defs lhs env a
             appConTop fc defs (reflectionttimp "IWithApp") [fc', f', a']
    reflect fc defs lhs env (ISearch tfc d)
        = do fc' <- reflect fc defs lhs env tfc
             d' <- reflect fc defs lhs env d
             appConTop fc defs (reflectionttimp "ISearch") [fc', d']
    reflect fc defs lhs env (IAlternative tfc t as)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             as' <- reflect fc defs lhs env as
             appConTop fc defs (reflectionttimp "IAlternative") [fc', t', as']
    reflect fc defs lhs env (IRewrite tfc t sc)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             sc' <- reflect fc defs lhs env sc
             appConTop fc defs (reflectionttimp "IRewrite") [fc', t', sc']
    reflect fc defs lhs env (ICoerced tfc d) = reflect fc defs lhs env d
    reflect fc defs lhs env (IBindHere tfc n sc)
        = do fc' <- reflect fc defs lhs env tfc
             n' <- reflect fc defs lhs env n
             sc' <- reflect fc defs lhs env sc
             appConTop fc defs (reflectionttimp "IBindHere") [fc', n', sc']
    reflect fc defs lhs env (IBindVar tfc n)
        = do fc' <- reflect fc defs lhs env tfc
             n' <- reflect fc defs lhs env n
             appConTop fc defs (reflectionttimp "IBindVar") [fc', n']
    reflect fc defs lhs env (IAs tfc nameFC s n t)
        = do fc' <- reflect fc defs lhs env tfc
             nameFC' <- reflect fc defs lhs env nameFC
             s' <- reflect fc defs lhs env s
             n' <- reflect fc defs lhs env n
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IAs") [fc', nameFC', s', n', t']
    reflect fc defs lhs env (IMustUnify tfc r t)
        = do fc' <- reflect fc defs lhs env tfc
             r' <- reflect fc defs lhs env r
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IMustUnify") [fc', r', t']
    reflect fc defs lhs env (IDelayed tfc r t)
        = do fc' <- reflect fc defs lhs env tfc
             r' <- reflect fc defs lhs env r
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IDelayed") [fc', r', t']
    reflect fc defs lhs env (IDelay tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IDelay") [fc', t']
    reflect fc defs lhs env (IForce tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IForce") [fc', t']
    reflect fc defs lhs env (IQuote tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IQuote") [fc', t']
    reflect fc defs lhs env (IQuoteName tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IQuoteName") [fc', t']
    reflect fc defs lhs env (IQuoteDecl tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IQuoteDecl") [fc', t']
    reflect fc defs lhs env (IUnquote tfc (IVar _ t))
        = pure (Ref tfc Bound t)
    reflect fc defs lhs env (IUnquote tfc t)
        = throw (InternalError "Can't reflect an unquote: escapes should be lifted out")
    reflect fc defs lhs env (IRunElab tfc t)
        = throw (InternalError "Can't reflect a %runElab")
    reflect fc defs lhs env (IPrimVal tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IPrimVal") [fc', t']
    reflect fc defs lhs env (IType tfc)
        = do fc' <- reflect fc defs lhs env tfc
             appConTop fc defs (reflectionttimp "IType") [fc']
    reflect fc defs lhs env (IHole tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IHole") [fc', t']
    reflect fc defs lhs env (IUnifyLog tfc _ t)
        = reflect fc defs lhs env t
    reflect fc defs True env (Implicit tfc t)
        = pure (Erased fc Placeholder)
    reflect fc defs lhs env (Implicit tfc t)
        = do fc' <- reflect fc defs lhs env tfc
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "Implicit") [fc', t']
    reflect fc defs lhs env (IWithUnambigNames tfc ns t)
        = do fc' <- reflect fc defs lhs env tfc
             ns' <- reflect fc defs lhs env ns
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "IWithUnambigNames") [fc', ns', t']

  export
  Reflect IFieldUpdate where
    reflect fc defs lhs env (ISetField p t)
        = do p' <- reflect fc defs lhs env p
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "ISetField") [p', t']
    reflect fc defs lhs env (ISetFieldApp p t)
        = do p' <- reflect fc defs lhs env p
             t' <- reflect fc defs lhs env t
             appConTop fc defs (reflectionttimp "ISetFieldApp") [p', t']

  export
  Reflect AltType where
    reflect fc defs lhs env FirstSuccess = getCon fc defs (reflectionttimp "FirstSuccess")
    reflect fc defs lhs env Unique = getCon fc defs (reflectionttimp "Unique")
    reflect fc defs lhs env (UniqueDefault x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "UniqueDefault") [x']

  export
  Reflect FnOpt where
    reflect fc defs lhs env Unsafe = getCon fc defs (reflectionttimp "Unsafe")
    reflect fc defs lhs env Inline = getCon fc defs (reflectionttimp "Inline")
    reflect fc defs lhs env NoInline = getCon fc defs (reflectionttimp "NoInline")
    reflect fc defs lhs env Deprecate = getCon fc defs (reflectionttimp "Deprecate")
    reflect fc defs lhs env TCInline = getCon fc defs (reflectionttimp "TCInline")
    reflect fc defs lhs env (Hint x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "Hint") [x']
    reflect fc defs lhs env (GlobalHint x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "GlobalHint") [x']
    reflect fc defs lhs env ExternFn = getCon fc defs (reflectionttimp "ExternFn")
    reflect fc defs lhs env (ForeignFn x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "ForeignFn") [x']
    reflect fc defs lhs env (ForeignExport x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "ForeignExport") [x']
    reflect fc defs lhs env Invertible = getCon fc defs (reflectionttimp "Invertible")
    reflect fc defs lhs env (Totality r)
        = do r' <- reflect fc defs lhs env r
             appConTop fc defs (reflectionttimp "Totality") [r']
    reflect fc defs lhs env Macro = getCon fc defs (reflectionttimp "Macro")
    reflect fc defs lhs env (SpecArgs r)
        = do r' <- reflect fc defs lhs env r
             appConTop fc defs (reflectionttimp "SpecArgs") [r']

  export
  Reflect ImpTy where
    reflect fc defs lhs env (MkImpTy w x y z)
        = do w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "MkTy") [w', x', y', z']

  export
  Reflect DataOpt where
    reflect fc defs lhs env (SearchBy x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "SearchBy") [x']
    reflect fc defs lhs env NoHints = getCon fc defs (reflectionttimp "NoHints")
    reflect fc defs lhs env UniqueSearch = getCon fc defs (reflectionttimp "UniqueSearch")
    reflect fc defs lhs env External = getCon fc defs (reflectionttimp "External")
    reflect fc defs lhs env NoNewtype = getCon fc defs (reflectionttimp "NoNewtype")

  export
  Reflect ImpData where
    reflect fc defs lhs env (MkImpData v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "MkData") [v', w', x', y', z']
    reflect fc defs lhs env (MkImpLater x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "MkLater") [x', y', z']

  export
  Reflect IField where
    reflect fc defs lhs env (MkIField v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "MkIField") [v', w', x', y', z']

  export
  Reflect ImpRecord where
    reflect fc defs lhs env (MkImpRecord v w x y z a)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             a' <- reflect fc defs lhs env a
             appConTop fc defs (reflectionttimp "MkRecord") [v', w', x', y', z', a']

  export
  Reflect WithFlag where
    reflect fc defs lhs env Syntactic
        = getCon fc defs (reflectionttimp "Syntactic")

  export
  Reflect ImpClause where
    reflect fc defs lhs env (PatClause x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "PatClause") [x', y', z']
    reflect fc defs lhs env (WithClause u v w x y z a)
        = do u' <- reflect fc defs lhs env u
             v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             a' <- reflect fc defs lhs env a
             appConTop fc defs (reflectionttimp "WithClause") [u', v', w', x', y', z', a']
    reflect fc defs lhs env (ImpossibleClause x y)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             appConTop fc defs (reflectionttimp "ImpossibleClause") [x', y']

  export
  Reflect ImpDecl where
    reflect fc defs lhs env (IClaim v w x y z)
        = do v' <- reflect fc defs lhs env v
             w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "IClaim") [v', w', x', y', z']
    reflect fc defs lhs env (IData x y z w)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             w' <- reflect fc defs lhs env w
             appConTop fc defs (reflectionttimp "IData") [x', y', z', w']
    reflect fc defs lhs env (IDef x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "IDef") [x', y', z']
    reflect fc defs lhs env (IParameters x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "IParameters") [x', y', z']
    reflect fc defs lhs env (IRecord w x y z u)
        = do w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             u' <- reflect fc defs lhs env u
             appConTop fc defs (reflectionttimp "IRecord") [w', x', y', z', u']
    reflect fc defs lhs env (IFail x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "IFail") [x', y', z']
    reflect fc defs lhs env (INamespace x y z)
        = do x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "INamespace") [x', y', z']
    reflect fc defs lhs env (ITransform w x y z)
        = do w' <- reflect fc defs lhs env w
             x' <- reflect fc defs lhs env x
             y' <- reflect fc defs lhs env y
             z' <- reflect fc defs lhs env z
             appConTop fc defs (reflectionttimp "ITransform") [w', x', y', z']
    reflect fc defs lhs env (IRunElabDecl w x)
        = throw (GenericMsg fc "Can't reflect a %runElab")
    reflect fc defs lhs env (IDirective _ _)
        = throw (GenericMsg fc "Can't reflect a directive")
    reflect fc defs lhs env (IPragma _ _ x)
        = throw (GenericMsg fc "Can't reflect a pragma")
    reflect fc defs lhs env (ILog x)
        = do x' <- reflect fc defs lhs env x
             appConTop fc defs (reflectionttimp "ILog") [x']
    reflect fc defs lhs env (IBuiltin _ _ _)
        = throw (GenericMsg fc "Can't reflect a %builtin")
