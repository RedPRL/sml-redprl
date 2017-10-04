structure Signature :> SIGNATURE =
struct
  structure Ar = RedPrlArity
  structure P = RedPrlSortData
  structure E = ElabMonadUtil (ElabMonad)
  structure ElabNotation = MonadNotation (E)
  structure AJ = RedPrlAtomicJudgment and Sort = RedPrlOpData and Hyps = RedPrlSequentData.Hyps

  open ElabNotation infix >>= *> <*

  fun @@ (f, x) = f x
  infixr @@

  open MiniSig
  structure O = RedPrlOpData and E = ElabMonadUtil (ElabMonad)

  fun intersperse s xs =
    case xs of
       [] => []
     | [x] => [x]
     | x::xs => Fpp.seq [x, s] :: intersperse s xs

  fun prettyArgs args =
    Fpp.Atomic.parens @@ Fpp.grouped @@ Fpp.hvsep @@
      intersperse (Fpp.text ";") @@
        List.map (fn (x, vl) => Fpp.hsep [Fpp.text (Metavar.toString x), Fpp.Atomic.colon, TermPrinter.ppValence vl]) args

  fun prettyEntry (_ : sign) (opid : symbol, entry as {spec, state,...} : entry) : Fpp.doc =
    let
      val arguments = entryArguments entry
      val state = state (fn _ => RedPrlSym.new ())
      val Lcf.|> (_, evd) = state
    in
      Fpp.hsep
        [Fpp.text "Def",
          Fpp.seq [Fpp.text @@ Sym.toString opid, prettyArgs arguments],
          Fpp.Atomic.colon,
          Fpp.grouped @@ Fpp.Atomic.squares @@ Fpp.seq
            [Fpp.nest 2 @@ Fpp.seq [Fpp.newline, RedPrlSequent.pretty spec],
            Fpp.newline],
          Fpp.Atomic.equals,
          Fpp.grouped @@ Fpp.Atomic.squares @@ Fpp.seq
            [Fpp.nest 2 @@ Fpp.seq [Fpp.newline, TermPrinter.ppBinder (Tm.outb evd)],
            Fpp.newline],
          Fpp.char #"."]
    end


  val empty =
    {sourceSign = Telescope.empty,
     elabSign = ETelescope.empty,
     nameEnv = NameEnv.empty}

  local
    val getEntry =
      fn EDEF entry => SOME entry
       | _ => NONE

    fun arityOfDecl (entry : entry) : Tm.psort list * Tm.O.Ar.t =
      let
        val arguments = entryArguments entry
        val sort = entrySort entry
      in
        ([], (List.map #2 arguments, sort))
      end

    structure OptionMonad = MonadNotation (OptionMonad)

    fun arityOfOpid (sign : sign) opid =
      let
        open OptionMonad infix >>=
      in
        NameEnv.find (#nameEnv sign) opid
          >>= ETelescope.find (#elabSign sign)
          >>= E.run
          >>= Option.map arityOfDecl o getEntry
      end

    structure Err = RedPrlError

    fun error pos msg = Err.raiseAnnotatedError' (pos, Err.GENERIC msg)

    (* During parsing, the arity of a custom-operator application is not known; but we can
     * derive it from the signature "so far". Prior to adding a declaration to the signature,
     * we process its terms to fill this in. *)
    local
      open RedPrlAst
      infix $ $$ $# $$# \


      fun inheritAnnotation t1 t2 =
        case getAnnotation t2 of
          NONE => setAnnotation (getAnnotation t1) t2
        | _ => t2

      fun guessSort varctx (tm : ast) : sort =
        case out tm of
           `x => (StringListDict.lookup varctx x handle _ => error (getAnnotation tm) [Fpp.text ("Could not resolve variable " ^ x)])
         | th $ _ =>
           let
             val (_, tau) = Tm.O.arity th
           in
             tau
           end
         | _ => O.EXP

      fun processOp pos sign varctx th  =
        case th of
           O.POLY (O.CUST (opid, NONE)) =>
           (case arityOfOpid sign opid of
               SOME (psorts, ar) => O.POLY (O.CUST (opid, SOME ar))
             | NONE => error pos [Fpp.text "Encountered undefined custom operator:", Fpp.text opid])
         | O.POLY (O.DEV_APPLY_LEMMA (opid, NONE, pat)) =>
           (case arityOfOpid sign opid of
               SOME (psorts, ar) => O.POLY (O.DEV_APPLY_LEMMA (opid, SOME ar, pat))
             | NONE => error pos [Fpp.text "Encountered undefined custom operator:", Fpp.text opid])
         | O.POLY (O.DEV_USE_LEMMA (opid, NONE)) =>
           (case arityOfOpid sign opid of
               SOME (psorts, ar) => O.POLY (O.DEV_USE_LEMMA (opid, SOME ar))
             | NONE => error pos [Fpp.text "Encountered undefined custom operator:", Fpp.text opid])
         | th => th

      and processTerm' sign varctx m =
        case out m of
           `x => ``x
         | O.MONO (O.MK_ANY NONE) $ [_ \ m] => 
           let
             val m' = processTerm sign varctx m
             val tau = guessSort varctx m
           in
             O.MONO (O.MK_ANY (SOME tau)) $$ [([],[]) \ m']
           end
         | th $ es =>
           let
             val th' = processOp (getAnnotation m) sign varctx th
             val (vls, _) = Tm.O.arity th'
             val es' = ListPair.map (fn (e, vl) => processBinder sign varctx vl e) (es, vls)
           in
             th' $$ es'
           end
         | x $# (ps, ms) => x $$# (ps, List.map (processTerm sign varctx) ms)

      and processBinder sign varctx ((sigmas, taus), _) ((us, xs) \ m) = 
        let
          val varctx' = ListPair.foldl (fn (x, tau, vars) => StringListDict.insert vars x tau) varctx (xs, taus)
        in
          (us, xs) \ processTerm sign varctx' m
        end

      and processTerm sign varctx m =
        inheritAnnotation m (processTerm' sign varctx m)

      fun processSrcCatjdg sign = processTerm sign

      fun catjdgEvidence jdg = 
        case out jdg of 
           O.MONO (O.JDG_TRUE _) $ _ => O.EXP
         | O.MONO (O.JDG_SYNTH _) $ _ => O.EXP
         | O.MONO (O.JDG_TERM tau) $ _ => tau
         | _ => O.TRIV

      fun processSrcHyps sign varctx hyps =
        case hyps of
           [] => ([], varctx)
         | (x, hyp) :: hyps => 
           let
             val hyp' = processSrcCatjdg sign varctx hyp
             val varctx' = StringListDict.insert varctx x (catjdgEvidence hyp')
             val (hyps', varctx'') = processSrcHyps sign varctx' hyps
           in
             ((x, hyp') :: hyps', varctx'')
           end

      fun processSrcSeq sign varctx (hyps, concl) = 
        let
          val (hyps', varctx') = processSrcHyps sign varctx hyps
        in
          (hyps', processSrcCatjdg sign varctx' concl)
        end

    in
      fun processDecl sign =
        fn DEF {arguments, sort, definiens} => DEF {arguments = arguments, sort = sort, definiens = processTerm sign StringListDict.empty definiens}
         | THM {arguments, goal, script} => THM {arguments = arguments, goal = processSrcSeq sign StringListDict.empty goal, script = processTerm sign StringListDict.empty script}
         | TAC {arguments, script} => TAC {arguments = arguments, script = processTerm sign StringListDict.empty script}
    end

    structure MetaCtx = Tm.Metavar.Ctx

    structure TacticElaborator = TacticElaborator (MiniSig)

    fun elabDeclArguments args =
      List.foldr
        (fn ((x, vl), (args', mctx)) =>
          let
            val x' = Metavar.named x
          in
            ((x', vl) :: args', MetaCtx.insert mctx x' vl)
          end)
        ([], MetaCtx.empty)
        args

    fun scopeCheck (metactx, symctx, varctx) term : Tm.abt E.t =
      let
        val termPos = Tm.getAnnotation term
        val symOccurrences = Susp.delay (fn _ => Tm.symOccurrences term)
        val varOccurrences = Susp.delay (fn _ => Tm.varOccurrences term)

        val checkSyms =
          Tm.Sym.Ctx.foldl
            (fn (u, tau, r) =>
              let
                val tau' = Tm.Sym.Ctx.find symctx u
                val ustr = Tm.Sym.toString u
                val pos =
                  case Tm.Sym.Ctx.find (Susp.force symOccurrences) u of
                      SOME (pos :: _) => SOME pos
                    | _ => (print ("couldn't find position for var " ^ ustr); termPos)
              in
                E.when (tau' = NONE, E.fail (pos, Fpp.text ("Unbound symbol: " ^ ustr)))
                  *> E.when (Option.isSome tau' andalso not (tau' = SOME tau), E.fail (pos, Fpp.text ("Symbol sort mismatch: " ^ ustr)))
                  *> r
              end)
            (E.ret ())
            (Tm.symctx term)

        val checkVars =
          Tm.Var.Ctx.foldl
            (fn (x, tau, r) =>
               let
                 val tau' = Tm.Var.Ctx.find varctx x
                 val xstr = Tm.Sym.toString x
                 val pos =
                   case Tm.Var.Ctx.find (Susp.force varOccurrences) x of
                      SOME (pos :: _) => SOME pos
                    | _ => termPos
               in
                 E.when (tau' = NONE, E.fail (pos, Fpp.hsep [Fpp.text "Unbound variable:", Fpp.text xstr]))
                  *> E.when (Option.isSome tau' andalso not (tau' = SOME tau), E.fail (pos, Fpp.text ("Variable sort mismatch: " ^ xstr)))
                  *> r
               end)
            (E.ret ())
            (Tm.varctx term)

        val checkMetas =
          Tm.Metavar.Ctx.foldl
            (fn (x, _, r) =>
               r <* E.unless (Option.isSome (Tm.Metavar.Ctx.find metactx x), E.fail (termPos, Fpp.text ("Unbound metavar: " ^ Tm.Metavar.toString x))))
            (E.ret ())
            (Tm.metactx term)
      in
        checkVars *> checkSyms *> checkMetas *> E.ret term
      end

    fun metactxToNameEnv metactx =
      Tm.Metavar.Ctx.foldl
        (fn (x, _, r) => AstToAbt.NameEnv.insert r (Tm.Metavar.toString x) x)
        AstToAbt.NameEnv.empty
        metactx

    fun convertToAbt (metactx, symctx, varctx, env) ast sort : abt E.t =
      E.wrap (RedPrlAst.getAnnotation ast, fn () =>
        AstToAbt.convertOpen (metactx, metactxToNameEnv metactx) (env, env) (ast, sort)
        handle AstToAbt.BadConversion (msg, pos) => error pos [Fpp.text msg])
      >>= scopeCheck (metactx, symctx, varctx)

    fun elabSrcCatjdg (metactx, symctx, varctx, env) ast : AJ.jdg E.t =
      convertToAbt (metactx, symctx, varctx, env) ast O.JDG >>= 
        E.ret o AJ.out

    fun addHypName (env, symctx, varctx) (srcname, tau) : symbol NameEnv.dict * Tm.symctx * Tm.varctx * Tm.symbol =
      let
        val x = NameEnv.lookup env srcname handle _ => Sym.named srcname
        val env' = NameEnv.insert env srcname x
        val varctx' = Sym.Ctx.insert varctx x tau
      in
        (env', symctx, varctx', x)
      end

    fun elabSrcSeqHyp (metactx, symctx, varctx, env) (srcname, srcjdg) : (Tm.symctx * Tm.varctx * symbol NameEnv.dict * symbol * AJ.jdg) E.t =
      elabSrcCatjdg (metactx, symctx, varctx, env) srcjdg >>= (fn catjdg => 
        let
          val tau = AJ.synthesis catjdg
          val (env', symctx', varctx', x) = addHypName (env, symctx, varctx) (srcname, tau)
        in
          E.ret (symctx', varctx', env', x, catjdg)
        end)

    fun elabSrcSeqHyps (metactx, symctx, varctx, env) : src_seqhyp list -> (Tm.symctx * Tm.varctx * symbol NameEnv.dict * AJ.jdg Hyps.telescope) E.t =
      let
        fun go env syms vars H [] = E.ret (syms, vars, env, H)
          | go env syms vars H (hyp :: hyps) =
              elabSrcSeqHyp (metactx, syms, vars, env) hyp >>= (fn (syms', vars', env', x, jdg) => 
                go env' syms' vars' (Hyps.snoc H x jdg) hyps)
      in
        go env symctx varctx Hyps.empty
      end

    fun elabSrcSequent (metactx, symctx, varctx, env) (seq : src_sequent) : (symbol NameEnv.dict * jdg) E.t =
      let
        val (hyps, concl) = seq
      in
        elabSrcSeqHyps (metactx, symctx, varctx, env) hyps >>= (fn (symctx', varctx', env', hyps') =>
          elabSrcCatjdg (metactx, symctx', varctx', env') concl >>= (fn concl' =>
             (* todo: I := ? *)
            E.ret (env', RedPrlSequent.>> (hyps', concl'))))
      end

    fun makeNamePopper alpha = 
      let
        val ix = ref 0
      in
        fn () => 
          let
            val i = !ix
            val h = alpha i
          in
            ix := i + 1;
            h
          end
      end

    fun valenceToSequent alpha ((sigmas, taus), tau) =
      let
        open RedPrlSequent AJ infix >>
        val fresh = makeNamePopper alpha
        val I = List.map (fn sigma => (fresh (), sigma)) sigmas
        val H = List.foldl (fn (tau, H) => Hyps.snoc H (fresh ()) (TERM tau)) Hyps.empty @@ List.rev taus
      in
        H >> TERM tau
      end

    fun argumentsToSubgoals alpha arguments = 
      List.foldr
        (fn ((x,vl), r) => Lcf.Tl.cons x (valenceToSequent alpha vl) r)
        Lcf.Tl.empty
        arguments


    fun globalNameSequence i = Sym.named ("@" ^ Int.toString i)


    fun initialEnv (sign : sign) : Tm.symctx * symbol NameEnv.dict =
      ETelescope.foldl
        (fn (x, _, (ctx, env)) => (Tm.Sym.Ctx.insert ctx x P.OPID, NameEnv.insert env (Tm.Sym.toString x) x))
        (Tm.Sym.Ctx.empty, NameEnv.empty)
        (#elabSign sign)
  

    fun elabDef (sign : sign) opid {arguments, sort, definiens} =
      let
        val (arguments', metactx) = elabDeclArguments arguments
        val (symctx, env) = initialEnv sign
      in
        convertToAbt (metactx, symctx, Var.Ctx.empty, env) definiens sort >>= (fn definiens' =>
          let
            val tau = sort
            open Tm infix \

            fun state alpha =
              let
                val binder = ([], []) \ definiens'
                val valence = (([], []), tau)
                val subgoals = argumentsToSubgoals alpha arguments'
              in
                Lcf.|> (subgoals, checkb (binder, valence))
              end

            val spec = RedPrlSequent.>> (Hyps.empty, AJ.TERM tau)
          in
            E.ret (EDEF {sourceOpid = opid, spec = spec, state = state})
          end)
      end

    local
      open RedPrlSequent Tm RedPrlOpData infix >> \ $$

      fun elabRefine sign alpha (seqjdg, script) =
        let
          val pos = getAnnotation script
        in
          E.wrap (pos, fn _ => TacticElaborator.tactic sign Var.Ctx.empty script alpha seqjdg)
        end

      structure Tl = TelescopeUtil (Lcf.Tl)

      fun checkProofState (pos, subgoalsSpec) state =
        let
          val Lcf.|> (subgoals, _) = state
          fun goalEqualTo goal1 goal2 =
            if RedPrlSequent.eq (goal1, goal2) then true
            else
              (RedPrlLog.print RedPrlLog.WARN (pos, Fpp.hvsep [RedPrlSequent.pretty goal1, Fpp.text "not equal to", RedPrlSequent.pretty goal2]);
               false)

          fun go ([], Tl.ConsView.EMPTY) = true
            | go (jdgSpec :: subgoalsSpec, Tl.ConsView.CONS (_, jdgReal, subgoalsReal)) =
                goalEqualTo jdgSpec jdgReal andalso go (subgoalsSpec, Tl.ConsView.out subgoalsReal)
            | go _ = false

          val proofStateCorrect = go (subgoalsSpec, Tl.ConsView.out subgoals)
          val subgoalsCount = Tl.foldr (fn (_,_,n) => 1 + n) 0 subgoals
        in
          if proofStateCorrect then
            E.ret state
          else
            E.warn (pos, Fpp.text (Int.toString (subgoalsCount) ^ " Remaining Obligations"))
              *> E.ret state
        end
    in

      fun elabThm sign opid pos {arguments, goal, script} =
        let
          val (arguments', metactx) = elabDeclArguments arguments
          val (symctx, env) = initialEnv sign
        in
          elabSrcSequent (metactx, symctx, Var.Ctx.empty, env) goal >>= (fn (_, seqjdg as hyps >> concl) =>
            let
              val seqjdg' = hyps >> concl
            in
              convertToAbt (metactx, symctx, Var.Ctx.empty, env) script TAC >>= 
              (fn scriptTm => elabRefine sign globalNameSequence (seqjdg', scriptTm)) >>= 
              checkProofState (pos, []) >>=
              (fn Lcf.|> (subgoals, validation) => 
                let
                  fun state alpha =
                    let
                      val argSubgoals = argumentsToSubgoals alpha arguments'
                      (* TODO: relabel ordinary subgoals using alpha too *)
                    in
                      Lcf.|> (Lcf.Tl.append argSubgoals subgoals, validation)
                    end
                in
                  E.ret @@ EDEF {sourceOpid = opid, spec = seqjdg', state = state}
                end)
            end)
        end
      end

    fun elabTac (sign : sign) opid {arguments, script} =
      let
        val (arguments', metactx) = elabDeclArguments arguments
        val (symctx, env) = initialEnv sign
      in
        convertToAbt (metactx, symctx, Var.Ctx.empty, env) script O.TAC >>= (fn script' =>
          let
            open O Tm infix \
            val binder = ([], []) \ script'
            val valence = (([], []), TAC)
            fun state alpha = Lcf.|> (argumentsToSubgoals alpha arguments', checkb (binder, valence))
            val spec = RedPrlSequent.>> (Hyps.empty, AJ.TERM TAC)
          in
            E.ret @@ EDEF {sourceOpid = opid, spec = spec, state = state}
          end)
      end

    fun elabDecl (sign : sign) (opid, eopid) (decl : src_decl, pos) : elab_sign =
      let
        val esign' = ETelescope.truncateFrom (#elabSign sign) eopid
        val sign' = {sourceSign = #sourceSign sign, elabSign = esign', nameEnv = #nameEnv sign}
      in
        ETelescope.snoc esign' eopid (E.delay (fn _ =>
          case processDecl sign decl of
             DEF defn => elabDef sign' opid defn
           | THM defn => elabThm sign' opid pos defn
           | TAC defn => elabTac sign' opid defn))
      end

    fun elabPrint (sign : sign) (pos, opid) =
      E.wrap (SOME pos, fn _ => NameEnv.lookup (#nameEnv sign) opid) >>= (fn eopid =>
        E.hush (ETelescope.lookup (#elabSign sign) eopid) >>= (fn edecl =>
          E.ret (ECMD (PRINT eopid)) <*
            (case edecl of
                EDEF entry => E.info (SOME pos, Fpp.vsep [Fpp.text "Elaborated:", prettyEntry sign (eopid, entry)])
              | _ => E.warn (SOME pos, Fpp.text "Invalid declaration name"))))

    local
      open Tm infix $ \
      fun printExtractOf (pos, state) : unit E.t =
        let
          val Lcf.|> (_, evd) = state
          val _ \ term = outb evd
        in
          E.info (SOME pos, Fpp.vsep [Fpp.text "Extract:", TermPrinter.ppTerm term])
        end
    in
      fun elabExtract (sign : sign) (pos, opid) =
        E.wrap (SOME pos, fn _ => NameEnv.lookup (#nameEnv sign) opid) >>= (fn eopid =>
          E.hush (ETelescope.lookup (#elabSign sign) eopid) >>= (fn edecl =>
            E.ret (ECMD (EXTRACT eopid)) <*
              (case edecl of
                  EDEF entry => printExtractOf (pos, #state entry (fn _ => RedPrlSym.new ()))
                | _ => E.warn (SOME pos, Fpp.text "Invalid declaration name"))))
    end

    fun elabCmd (sign : sign) (cmd, pos) : elab_sign =
      case cmd of
         PRINT opid =>
           let
             val fresh = Sym.named "_"
           in
             ETelescope.snoc (#elabSign sign) fresh (E.delay (fn _ => elabPrint sign (pos, opid)))
           end
       | EXTRACT opid =>
           let
             val fresh = Sym.named "_"
           in
             ETelescope.snoc (#elabSign sign) fresh (E.delay (fn _ => elabExtract sign (pos, opid)))
           end


    fun insertAstDecl sign opid (decl, pos) =
      let
        val sign' = Telescope.truncateFrom sign opid
      in
        Telescope.snoc sign' opid (decl, pos)
      end
      handle Telescope.Duplicate l => error pos [Fpp.text "Duplicate identitifier:", Fpp.text l]

  in
    fun insert (sign : sign) opid (decl, pos) =
      let
        val sourceSign = insertAstDecl (#sourceSign sign) opid (decl, pos)

        val eopid = Tm.Sym.named opid
        val elabSign = elabDecl sign (opid, eopid) (decl, pos)
        val nameEnv = NameEnv.insert (#nameEnv sign) opid eopid
      in
        {sourceSign = sourceSign, elabSign = elabSign, nameEnv = nameEnv}
      end

    fun command (sign : sign) (cmd, pos) =
      let
        val elabSign = elabCmd sign (cmd, pos)
      in
        {sourceSign = #sourceSign sign, elabSign = elabSign, nameEnv = #nameEnv sign}
      end
  end

  structure L = RedPrlLog

  val checkAlg : (elab_decl, bool) E.alg =
    {warn = fn (msg, _) => (L.print L.WARN msg; false),
     info = fn (msg, r) => (L.print L.INFO msg; r),
     dump = fn (msg, r) => (L.print L.DUMP msg; r),
     init = true,
     succeed = fn (_, r) => r,
     fail = fn (msg, _) => (L.print L.FAIL msg; false)}

  fun check ({elabSign,...} : sign) =
    ETelescope.foldl (fn (_, e, r) => E.fold checkAlg e andalso r) true elabSign
end
