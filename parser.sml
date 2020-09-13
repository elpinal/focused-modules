structure ParserError = struct
  exception UnexpectedToken of Token.token option
  exception ForbiddenExistentialSignature
end

structure Parser = MakeParser (struct
  structure Streamable = StreamStreamable
  structure Arg = struct
    val disallow_existential_signature = true

    open Std

    open ParserError

    type string = string

    type program = module
    type module = module
    type tycon = tycon
    type kind = kind
    type tvar = tvar
    type sign = sign
    type pos_sig = pos_sig
    type term = term
    type lax_module = lax_module
    type existential = kind * tycon
    type term_params = (var * tycon) list

    fun program_module x = x
    fun module_atom x = x
    fun module_app x = x
    fun module_paren x = x
    val mvar = MVar
    fun mstar () = MStar
    fun mstatic ty = MStatic ty
    fun mdynamic e = MDynamic e
    fun mpair (x, y) = MPair (x, y)
    val mapp = MApp
    fun mfst x = MProj(Fst, x)
    fun msnd x = MProj(Snd, x)
    fun mabs (v, mv, s, x) = MAbs(mv, s, close_at_module 0 v x)
    fun mlet (v, e, x) = MLet(v, e, x)
    fun mletmodule (v, mv, x, y) = MLetModule(mv, x, close_at_module 0 v y)
    fun mcirc l = MCirc l

    fun lret m = LRet m
    fun lseal (m, s) = LSeal(m, s)
    fun lbind (v, mv, m, x) = LBind(mv, m, close_at_lax_module 0 v x)
    fun lunpack (v, ev, e, x) = LUnpack(ev, e, close_at_lax_module 0 v x)

    fun type_paren x = x
    fun type_bin x = x
    fun type_app x = x
    fun type_atom x = x
    fun quote_ident s = TVar.from_string s
    fun tvar_ v = TFree v
    fun tabs (v, k, ty) = TAbs(k, close_at_tycon 0 v ty)
    fun tstar () = TStar
    fun tunit () = TUnit
    val tpair = TPair
    val tapp = TApp
    fun tfst x = TProj(Fst, x)
    fun tsnd x = TProj(Snd, x)
    val tarrow = TArrow
    val tprod = TProd
    fun tforall (v, k, ty) = TForall(k, close_at_tycon 0 v ty)
    fun exist (v, k, ty) = (k, close_at_tycon 0 v ty)
    fun texist x = TExist x

    fun kunit () = KUnit
    fun ktype () = KType
    val ksingleton = KSingleton
    fun karrow (v, x, y) = KArrow(x, close_at_kind 0 v y)
    fun kprod (v, x, y) = KProd(x, close_at_kind 0 v y)

    fun sunit () = SUnit
    val sstatic = SStatic
    val sdynamic = SDynamic
    fun sarrow (v, x, y) = SArrow(x, close_at_sig 0 v y)
    fun sprod (v, x, y) = SProd(x, close_at_sig 0 v y)
    val smonad = SMonad

    fun pos_sig_id x = x
    val pdown = PDown
    fun pexist (v, k, p) =
      if disallow_existential_signature
      then raise ForbiddenExistentialSignature
      else PExist(k, close_at_pos_sig 0 v p)

    fun term_id x = x
    fun empty_term_params () = []
    fun cons_term_params (v, ty, xs) = (v, ty) :: xs
    val evar = EVar
    fun estar () = EStar
    val epair = EPair
    val eapp = EApp
    val eext = EExt
    val efix = EFix
    fun efst x = EProj(Fst, x)
    fun esnd x = EProj(Snd, x)
    val einst = EInst
    fun eabs (xs, e) = foldr (fn ((v, ty), acc) => EAbs(v, ty, acc)) e xs
    fun egen (v, k, x) = EGen(k, close_at_term 0 v x)
    fun epack (w, x, (k, ty)) = EPack(w, x, k, ty)
    val elet = ELet
    fun eletlax (v, mv, l, x) = ELetLax(mv, l, close_at_term 0 v x)
    fun eunpack (v, ev, x, y) = EUnpack(ev, x, close_at_term 0 v y)

    datatype terminal = datatype Token.token

    fun error s = UnexpectedToken(SOME(Stream.hd s) handle Stream.Empty => NONE)
  end
end)
