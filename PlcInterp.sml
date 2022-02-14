(* PlcInterp *)

exception Impossible
exception HDEmptySeq
exception TLEmptySeq
exception ValueNotFoundInMatch
exception NotAFunc

fun eval (e:expr) (env:plcVal env) : plcVal =
	case e of
			ConI i => IntV i
		| ConB b => BoolV b
		| ESeq (SeqT t) => SeqV([])
		| Var x => lookup env x
		| Let(x, e1, e2) =>
				let
					val v = eval e1 env
					val env2 = (x,v) :: env
				in
					eval e2 env2
				end
		| Letrec(funName, argType, arg, funType, e1, e2) => eval e2 ((funName, Clos(funName, arg, e1, env))::env)
		| Prim1(opr, e1) =>
        let
          val v1 = eval e1 env
        in
          case (opr, v1) of
            	("-", IntV i) => IntV(~i)
						| ("print", _) => 
							let
								val s = val2string v1
							in
								print(s^"\n"); ListV []
							end
						| ("!", BoolV(b)) => BoolV(not(b))
						| ("hd", SeqV(s)) => if (s = []) then raise HDEmptySeq else hd(s)
						| ("tl", SeqV(s)) => if (s = []) then raise TLEmptySeq else SeqV(tl(s))
						| ("ise", SeqV(s)) => BoolV(s = [])
						| _ => raise Impossible
        end
    | Prim2(opr, e1, e2) =>
        let
          val v1 = eval e1 env
          val v2 = eval e2 env
        in
          case (opr, v1, v2) of 
							("*", IntV i1, IntV i2) => IntV (i1 * i2)
            | ("/", IntV i1, IntV i2) => IntV (i1 div i2)
            | ("+", IntV i1, IntV i2) => IntV (i1 + i2)
            | ("-", IntV i1, IntV i2) => IntV (i1 - i2)
            | (";", _, _) => v2
            | ("&&", BoolV b1, BoolV b2) => BoolV (b1 andalso b2)
            | ("::", BoolV b, SeqV s) => SeqV(BoolV(b)::s)
            | ("::", IntV n, SeqV s) => SeqV(IntV(n)::s)
            | ("::", ListV l, SeqV s) => SeqV(ListV(l)::s)
            | ("::", SeqV(s1), SeqV(s2)) => SeqV(SeqV(s1)::s2)
            | ("::", Clos c, SeqV s) => SeqV(Clos(c)::s)
            | ("<", IntV i1, IntV i2) => BoolV(i1 < i2)
            | ("<=", IntV i1, IntV i2) => BoolV(i1 <= i2)
            | ("=", IntV i1, IntV i2) => BoolV(i1 = i2)
            | ("=", BoolV b1, BoolV b2) => BoolV(b1 = b2)
            | ("=", ListV l1, ListV l2) => BoolV(l1 = l2)
            | ("=", SeqV s1, SeqV s2) => BoolV(s1 = s2)
            | ("!=", IntV i1, IntV i2) => BoolV(i1 <> i2)
            | ("!=", BoolV b1, BoolV b2) => BoolV(b1 <> b2)
            | ("!=", ListV l1, ListV l2) => BoolV(l1 <> l2)
            | ("!=", SeqV s1, SeqV s2) => BoolV(s1 <> s2)
						| _ => raise Impossible
        end
		| If(e1, e2, e3) =>
				let
					val condition = eval e1 env
				in
					case condition of
						 BoolV b => if b then eval e2 env else eval e3 env
						| _ => raise Impossible
				end
		| Match (expr, mtchExpr) =>
				if (mtchExpr = []) then 
						raise Impossible 
				else 
						let
							val evalue = eval expr env
							val matchCond = 
									fn (cond, resul) => ( 
										case cond of
											 NONE => true
											| SOME(e) => ((eval e env) = evalue)
									)
							val filterList = List.filter matchCond mtchExpr
						in
							if (filterList = []) then 
									raise ValueNotFoundInMatch 
							else 
									let 
										val matchexpr = hd filterList
										val resulE = (#2 matchexpr)
									in
										eval resulE env
									end
						end
		| Call(e1, e2) =>
				let
					val f = eval e1 env
				in
					case f of
							Clos(funName, arg, funExpr, envC) => 
								let
									val ev = eval e2 env
									val funEnv = (funName, f)::(arg, ev)::envC
								in
									eval funExpr funEnv
								end
							| _ => raise NotAFunc
				end
		| List [] => ListV []
		| List l => 
				if ((length l) > 1) then
					ListV (map (fn (x) => eval x env) l)
				else
					raise Impossible
		| Item (i, expr) =>
				let
					val eExpr = eval expr env
				in
					case eExpr of
							 ListV l => List.nth (l, i-1)
							| _ => raise Impossible
				end
		| Anon(argType, arg, e1) => Clos("", arg, e1, env)
		| _ => raise Impossible
