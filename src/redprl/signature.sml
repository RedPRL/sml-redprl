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

  fun prettyEntry (_ : sign) (opid : opid, entry as {spec, state,...} : entry) : Fpp.doc =
    let
      val arguments = entryArguments entry
      val state = state (fn _ => RedPrlSym.new ())
      val Lcf.|> (_, evd) = state
    in
      Fpp.hsep
        [Fpp.text "Def",
          Fpp.seq [Fpp.text opid, prettyArgs arguments],
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
     elabSign = Telescope.empty,
     nameEnv = NameEnv.empty}

  local
    val getEntry =
      fn EDEF entry => SOME entry
       | _ => NONE

    fun arityOfDecl (entry : entry) : Tm.O.Ar.t =
      let
        val arguments = entryArguments entry
        val sort = entrySort entry
      in
        (List.map #2 arguments, sort)
      end

    structure OptionMonad = MonadNotation (OptionMonad)

    fun arityOfOpid (sign : sign) opid =
      let
        open OptionMonad infix >>=
      in
        Telescope.find (#elabSign sign) opid
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


      fun catjdgEvidence jdg = 
        case out jdg of 
           O.JDG_TRUE $ _ => O.EXP
         | O.JDG_SYNTH $ _ => O.EXP
         | O.JDG_TERM tau $ _ => tau
         | _ => O.TRV

      fun lookupArity sign pos opid = 
        case arityOfOpid sign opid of
           SOME ar => ar
         | NONE => error pos [Fpp.text "Encountered undefined custom operator:", Fpp.text opid]

      fun guessSort sign varctx (tm : ast) : sort =
        case out tm of
           `x => (StringListDict.lookup varctx x handle _ => error (getAnnotation tm) [Fpp.text ("Could not resolve variable " ^ x)])
         | O.CUST (opid, _) $ _ => #2 (lookupArity sign (getAnnotation tm) opid)
         | th $ _ =>
           let
             val (_, tau) = Tm.O.arity th
           in
             tau
           end
         | _ => O.EXP

      fun processOp pos sign varctx th  =
        case th of
           O.CUST (opid, NONE) => O.CUST (opid, SOME (lookupArity sign pos opid))
         | O.DEV_APPLY_LEMMA (opid, NONE, pat) => O.DEV_APPLY_LEMMA (opid, SOME (lookupArity sign pos opid), pat)
         | O.DEV_USE_LEMMA (opid, NONE) => O.DEV_USE_LEMMA (opid, SOME (lookupArity sign pos opid))
         | th => th

      and processTerm' sign varctx m =
        case out m of
           `x => ``x
         | O.MK_ANY NONE $ [_ \ m] => 
           let
             val m' = processTerm sign varctx m
             val tau = guessSort sign varctx m
           in
             O.MK_ANY (SOME tau) $$ [[] \ m']
           end
         | O.DEV_LET NONE $ [_ \ jdg, _ \ tac1, tac2] =>
           let
             val jdg' = processTerm' sign varctx jdg
             val tau = catjdgEvidence jdg
             val tac1' = processTerm' sign varctx tac1
             val tac2' = processBinder sign varctx ([tau], O.TAC) tac2
           in
             O.DEV_LET (SOME tau) $$ [[] \ jdg', [] \ tac1', tac2']
           end
         | th $ es =>
           let
             val th' = processOp (getAnnotation m) sign varctx th
             val (vls, _) = Tm.O.arity th'
             val es' = ListPair.map (fn (e, vl) => processBinder sign varctx vl e) (es, vls)
           in
             th' $$ es'
           end
         | x $# ms => x $$# List.map (processTerm sign varctx) ms

      and processBinder sign varctx (taus, _) (xs \ m) = 
        let
          val varctx' = ListPair.foldl (fn (x, tau, vars) => StringListDict.insert vars x tau) varctx (xs, taus)
        in
          xs \ processTerm sign varctx' m
        end

      and processTerm sign varctx m =
        inheritAnnotation m (processTerm' sign varctx m)

      fun processSrcCatjdg sign = processTerm sign


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

    fun scopeCheck (metactx, varctx) term : Tm.abt E.t =
      let
        val termPos = Tm.getAnnotation term
        val varOccurrences = Susp.delay (fn _ => Tm.varOccurrences term)

        val checkVars =
          Tm.Var.Ctx.foldl
            (fn (x, tau, r) =>
               let
                 val tau' = Tm.Var.Ctx.find varctx x
                 val xstr = Tm.Var.toString x
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
        checkVars *> checkMetas *> E.ret term
      end

    fun metactxToNameEnv metactx =
      Tm.Metavar.Ctx.foldl
        (fn (x, _, r) => AstToAbt.NameEnv.insert r (Tm.Metavar.toString x) x)
        AstToAbt.NameEnv.empty
        metactx

    fun convertToAbt (metactx, varctx, env) ast sort : abt E.t =
      E.wrap (RedPrlAst.getAnnotation ast, fn () =>
        AstToAbt.convertOpen (metactx, metactxToNameEnv metactx) env (ast, sort)
        handle AstToAbt.BadConversion (msg, pos) => error pos [Fpp.text msg])
      >>= scopeCheck (metactx, varctx)

    fun elabSrcCatjdg (metactx, varctx, env) ast : AJ.jdg E.t =
      convertToAbt (metactx, varctx, env) ast O.JDG >>= 
        E.ret o AJ.out

    fun addHypName (env, varctx) (srcname, tau) : variable NameEnv.dict * Tm.varctx * Tm.variable =
      let
        val x = NameEnv.lookup env srcname handle _ => Sym.named srcname
        val env' = NameEnv.insert env srcname x
        val varctx' = Sym.Ctx.insert varctx x tau
      in
        (env', varctx', x)
      end

    fun elabSrcSeqHyp (metactx, varctx, env) (srcname, srcjdg) : (Tm.varctx * variable NameEnv.dict * variable * AJ.jdg) E.t =
      elabSrcCatjdg (metactx, varctx, env) srcjdg >>= (fn catjdg => 
        let
          val tau = AJ.synthesis catjdg
          val (env', varctx', x) = addHypName (env, varctx) (srcname, tau)
        in
          E.ret (varctx', env', x, catjdg)
        end)

    fun elabSrcSeqHyps (metactx, varctx, env) : src_seqhyp list -> (Tm.varctx * variable NameEnv.dict * AJ.jdg Hyps.telescope) E.t =
      let
        fun go env vars H [] = E.ret (vars, env, H)
          | go env vars H (hyp :: hyps) =
              elabSrcSeqHyp (metactx, vars, env) hyp >>= (fn (vars', env', x, jdg) => 
                go env' vars' (Hyps.snoc H x jdg) hyps)
      in
        go env varctx Hyps.empty
      end

    fun elabSrcSequent (metactx, varctx, env) (seq : src_sequent) : (variable NameEnv.dict * jdg) E.t =
      let
        val (hyps, concl) = seq
      in
        elabSrcSeqHyps (metactx, varctx, env) hyps >>= (fn (varctx', env', hyps') =>
          elabSrcCatjdg (metactx, varctx', env') concl >>= (fn concl' =>
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

    fun valenceToSequent alpha (taus, tau) =
      let
        open RedPrlSequent AJ infix >>
        val fresh = makeNamePopper alpha
        val H = List.foldl (fn (tau, H) => Hyps.snoc H (fresh ()) (TERM tau)) Hyps.empty @@ List.rev taus
      in
        H >> TERM tau
      end

    fun argumentsToSubgoals alpha arguments = 
      List.foldr
        (fn ((x,vl), r) => Lcf.Tl.cons x (valenceToSequent alpha vl) r)
        Lcf.Tl.empty
        arguments


    fun globalNameSequence i = Sym.named ("_" ^ Int.toString i)

    fun initialEnv (sign : sign) : variable NameEnv.dict =
      NameEnv.empty
  

    fun elabDef (sign : sign) opid {arguments, sort, definiens} =
      let
        val (arguments', metactx) = elabDeclArguments arguments
        val env = initialEnv sign
      in
        convertToAbt (metactx, Var.Ctx.empty, env) definiens sort >>= (fn definiens' =>
          let
            val tau = sort
            open Tm infix \

            fun state alpha =
              let
                val binder = [] \ definiens'
                val valence = ([], tau)
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
          E.wrap (pos, fn _ => Lcf.M.run (Lcf.complete (TacticElaborator.tactic sign Var.Ctx.empty script alpha) seqjdg))
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
          val env = initialEnv sign
        in
          elabSrcSequent (metactx, Var.Ctx.empty, env) goal >>= (fn (_, seqjdg as hyps >> concl) =>
            let
              val seqjdg' = hyps >> concl
            in
              convertToAbt (metactx, Var.Ctx.empty, env) script TAC >>= 
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
        val env = initialEnv sign
      in
        convertToAbt (metactx, Var.Ctx.empty, env) script O.TAC >>= (fn script' =>
          let
            open O Tm infix \
            val binder = [] \ script'
            val valence = ([], TAC)
            fun state alpha = Lcf.|> (argumentsToSubgoals alpha arguments', checkb (binder, valence))
            val spec = RedPrlSequent.>> (Hyps.empty, AJ.TERM TAC)
          in
            E.ret @@ EDEF {sourceOpid = opid, spec = spec, state = state}
          end)
      end

    fun elabDecl (sign : sign) opid (decl : src_decl, pos) : elab_sign =
      let
        val esign' = Telescope.truncateFrom (#elabSign sign) opid
        val sign' = {sourceSign = #sourceSign sign, elabSign = esign', nameEnv = #nameEnv sign}
      in
        Telescope.snoc esign' opid (E.delay (fn _ =>
          case processDecl sign decl of
             DEF defn => elabDef sign' opid defn
           | THM defn => elabThm sign' opid pos defn
           | TAC defn => elabTac sign' opid defn))
      end

    fun elabPrint (sign : sign) (pos, opid : opid) =
      E.hush (Telescope.lookup (#elabSign sign) opid) >>= (fn edecl =>
        E.ret (ECMD (PRINT opid)) <*
          (case edecl of
              EDEF entry => E.info (SOME pos, Fpp.vsep [Fpp.text "Elaborated:", prettyEntry sign (opid, entry)])
            | _ => E.warn (SOME pos, Fpp.text "Invalid declaration name")))

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
        E.hush (Telescope.lookup (#elabSign sign) opid) >>= (fn edecl =>
          E.ret (ECMD (EXTRACT opid)) <*
            (case edecl of
                EDEF entry => printExtractOf (pos, #state entry (fn _ => RedPrlSym.new ()))
              | _ => E.warn (SOME pos, Fpp.text "Invalid declaration name")))
    end

    fun elabCmd (sign : sign) (cmd, pos) : elab_sign =
      case cmd of
         PRINT opid =>
           let
             (* TODO: weird *)
             val fresh = Sym.DebugShow.toString (Sym.named "_")
           in
             Telescope.snoc (#elabSign sign) fresh (E.delay (fn _ => elabPrint sign (pos, opid)))
           end
       | EXTRACT opid =>
           let
             (* TODO: weird *)
             val fresh = Sym.DebugShow.toString (Sym.named "_")
           in
             Telescope.snoc (#elabSign sign) fresh (E.delay (fn _ => elabExtract sign (pos, opid)))
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
        val elabSign = elabDecl sign opid (decl, pos)
      in
        {sourceSign = sourceSign, elabSign = elabSign, nameEnv = #nameEnv sign}
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
    Telescope.foldl (fn (_, e, r) => E.fold checkAlg e andalso r) true elabSign
end
