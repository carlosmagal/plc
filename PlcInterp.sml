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
		| Letrec(funName, argType, arg, funType, expr1, expr2) =>
      	let 
        	val closureEnv = (funName, Clos(funName, arg, expr1, env))::env
      	in
        	eval expr2 closureEnv
      	end
		| Prim1(ope, expr1) =>
        let
          val val1 = eval expr1 env
        in
          case ope of
            ("!") => 
              let in
                case val1 of
                  BoolV(b) => BoolV(not(b))
                | _ => raise Impossible
              end
          | ("-") => 
              let in
                case val1 of
                  IntV(n) => IntV(~n)
                | _ => raise Impossible
              end
          | ("hd") => 
              let in
                case val1 of
                  SeqV(s) => if (s = []) then raise HDEmptySeq else hd(s)
                | _ => raise Impossible
              end
          | ("tl") => 
              let in
                case val1 of
                  SeqV(s) => if (s = []) then raise TLEmptySeq else SeqV(tl(s))
                | _ => raise Impossible
              end
          | ("ise") => 
              let in
                case val1 of
                  SeqV(s) => BoolV(s = [])
                | _ => raise Impossible
              end
          | ("print") => 
              let
                val env = print(val2string(val1)^"\n")
              in
                ListV([])
              end
          | _ => raise Impossible
        end
    | Prim2(ope, expr1, expr2) =>
        let
          val val1 = eval expr1 env
          val val2 = eval expr2 env
        in
          case ope of 
              ("&&") => 
                let in
                  case (val1, val2) of
                    (BoolV(b1), BoolV(b2)) => BoolV(b1 andalso b2)
                  | _ => raise Impossible
                end
            | ("::") => 
                let in
                  case (val1, val2) of
                    (BoolV(b), SeqV(s)) => SeqV(BoolV(b)::s)
                  | (IntV(n), SeqV(s)) => SeqV(IntV(n)::s)
                  | (ListV(l), SeqV(s)) => SeqV(ListV(l)::s)
                  | (SeqV(s1), SeqV(s2)) => SeqV(SeqV(s1)::s2)
                  | (Clos(c), SeqV(s)) => SeqV(Clos(c)::s)
                  | _ => raise Impossible
                end
            | ("+") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => IntV(n1 + n2)
                  | _ => raise Impossible
                end
            | ("*") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => IntV(n1 * n2)
                  | _ => raise Impossible
                end
            | ("-") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => IntV(n1 - n2)
                  | _ => raise Impossible
                end
            | ("/") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => IntV(n1 div n2)
                  | _ => raise Impossible
                end
            | ("<") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => BoolV(n1 < n2)
                  | _ => raise Impossible
                end
            | ("<=") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => BoolV(n1 <= n2)
                  | _ => raise Impossible
                end
            | ("=") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => BoolV(n1 = n2)
                  | (BoolV(b1), BoolV(b2)) => BoolV(b1 = b2)
                  | (ListV(l1), ListV(l2)) => BoolV(l1 = l2)
                  | (SeqV(s1), SeqV(s2)) => BoolV(s1 = s2)
                  | _ => raise Impossible
                end
            | ("!=") => 
                let in
                  case (val1, val2) of
                    (IntV(n1), IntV(n2)) => BoolV(n1 <> n2)
                  | (BoolV(b1), BoolV(b2)) => BoolV(b1 <> b2)
                  | (ListV(l1), ListV(l2)) => BoolV(l1 <> l2)
                  | (SeqV(s1), SeqV(s2)) => BoolV(s1 <> s2)
                  | _ => raise Impossible
                end
            | (";") => val2
          | _ => raise Impossible
        end
		| If(expr1, expr2, expr3) =>
				let
					val condition = eval expr1 env
				in
					case condition of
						 BoolV b => if b then eval expr2 env else eval expr3 env
						| _ => raise Impossible
				end
		| Match (expr, mtchExpr) =>
				if (mtchExpr = []) then 
						raise Impossible 
				else 
						let
							val exprVal = eval expr env
							val matchCondition = 
									fn (condExpr, resultExpr) => ( 
										case condExpr of
											 NONE => true
											| SOME(e) => 
												let
													val cond = eval e env
												in
													(cond = exprVal)
												end
									)
							val filterList = List.filter matchCondition mtchExpr
						in
							if (filterList = []) then 
									raise ValueNotFoundInMatch 
							else 
									let 
										val matchedExpr = hd filterList
										val resultExpr = (#2 matchedExpr)
									in
										eval resultExpr env
									end
						end
		| Call(expr1, expr2) =>
				let
					val f = eval expr1 env
				in
					case f of
							Clos(funName, arg, funExpr, envC) => 
								let
									val ev = eval expr2 env
									val funEnv = (funName, f)::(arg, ev)::envC
								in
									eval funExpr funEnv
								end
							| _ => raise NotAFunc
				end
		| List [] => ListV []
		| List l => 
				if (length l) > 1 then
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
		| Anon(argType, arg, expr1) => Clos("", arg, expr1, env)
		| _ => raise Impossible
