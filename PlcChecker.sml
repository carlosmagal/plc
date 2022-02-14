(* PlcChecker *)

exception EmptySeq 
exception UnknownType 
exception NotEqTypes 
exception WrongRetType 
exception DiffBrTypes 
exception IfCondNotBool 
exception NoMatchResults 
exception MatchResTypeDiff 
exception MatchCondTypesDiff 
exception CallTypeMisM 
exception NotFunc 
exception ListOutOfRange 
exception OpNonList 

fun teval (e:expr) (env:plcType env) : plcType = 
    case e of
      ConI(_) => IntT 
    | ConB(_) => BoolT 
    | ESeq (SeqT t) => SeqT(t)
    | Var x => lookup env x
    | Let(x, e1, e2) => 
      let
        val t = teval e1 env
        val env' = (x, t)::env
      in
        teval e2 env'
      end
    | Letrec(funName, argType, arg, funType, expr1, expr2) => 
      let
        val envFun = (funName, FunT(argType, funType))
        val envArgs = (arg, argType)
        val type1 = teval expr1 (envFun::envArgs::env)
      in
        if(type1 = funType) then teval expr2 (envFun::env) else raise WrongRetType
      end
    | Prim1(opr, expr1) =>
      let
        val t1 = teval expr1 env
      in
        case (opr, t1) of
            ("print", _) => ListT []
          | ("hd", _) => 
            let in
              case expr1 of
                ESeq(SeqT(t)) => raise EmptySeq
              | _ => 
                let in
                  case t1 of
                    SeqT(t) => t
                  | _ => raise UnknownType
                end
            end
          | ("tl",_) => 
            let in
              case expr1 of
                ESeq(SeqT(t)) => raise EmptySeq
              | _ => 
                let in
                  case t1 of
                    SeqT(t) => SeqT(t)
                  | _ => raise UnknownType
                end
            end
          | ("-", IntT) => IntT
          | ("!", BoolT) => BoolT
          | ("ise",_) => 
            let in
              case t1 of
                SeqT(t) => BoolT
              | _ => raise UnknownType
            end
          | _ => raise UnknownType
      end
    | Prim2(opr, e1, e2) =>
      let
        val t1 = teval e1 env
        val t2 = teval e2 env
      in
        case (opr, t1, t2) of
           ("*", IntT, IntT) => IntT
          | ("/", IntT, IntT) => IntT
          | ("+", IntT, IntT) => IntT
          | ("-", IntT, IntT) => IntT
          | (";", _, _) => t2
          | ("&&", _, _) => if (t1 = t2) then BoolT else raise UnknownType
          | ("::", _, _) => if (t2 = SeqT(t1)) then SeqT(t1) else raise UnknownType
          | ("<", IntT, IntT) => BoolT
          | ("<=", IntT, IntT) => BoolT
          | ("=", _, _) => 
            if (t1 <> t2) then 
              raise NotEqTypes 
            else
              let in
                case t1 of
                  BoolT => BoolT
                | IntT => BoolT
                | ListT([]) => BoolT
                | SeqT(seqType) =>
                    let in
                      case seqType of
                          BoolT => BoolT
                        | IntT => BoolT
                        | ListT([]) => BoolT
                        | _ => raise NotEqTypes
                    end
                | ListT(tlist) => 
                  let
                    val list = map(fn(t) => 
                        case t of
                            BoolT => BoolT
                          | IntT => IntT
                          | ListT([]) => ListT([])
                          | _ => raise NotEqTypes
                      ) 
                      tlist
                  in
                    BoolT
                  end
                | _ => raise UnknownType
              end
          | ("!=", _, _) => 
            if(t1 <> t2) then 
              raise NotEqTypes 
            else
              let in
                case t1 of
                  BoolT => BoolT
                | IntT => BoolT
                | ListT([]) => BoolT
                | SeqT(seqType) =>
                  let in
                    case seqType of
                        BoolT => BoolT
                      | IntT => BoolT
                      | ListT([]) => BoolT
                      | _ => raise NotEqTypes
                  end
                | ListT(tlist) => 
                  let
                    val list = map(fn(t) => 
                        case t of
                            BoolT => BoolT
                          | IntT => IntT
                          | ListT([]) => ListT([])
                          | _ => raise NotEqTypes) 
                      tlist
                  in
                    BoolT
                  end
                | _ => raise UnknownType
              end
          | _ => raise UnknownType
      end
    | If(e1, e2, e3) =>
      let
        val t1 = teval e1 env
        val t2 = teval e2 env
        val t3 = teval e3 env
      in
        if(t1 <> BoolT) then 
          raise IfCondNotBool 
        else 
          if(t2 <> t3) then 
            raise DiffBrTypes 
          else 
            t3
      end
    | Match (e1, matchExpr) => 
      if(matchExpr = []) then 
        raise NoMatchResults 
      else 
        let
          val etype = teval e1 env
          val tlist = map (
            fn (cond, resul) => ( 
              case cond of
                  NONE => teval resul env
                | SOME e => 
                  let
                    val condtype = teval e env
                  in
                    if (condtype = etype) then 
                      teval resul env 
                    else 
                      raise MatchCondTypesDiff
                  end
            )) matchExpr
        in
          hd tlist
        end
    | Call(e1, e2) =>
      let
        val t1 = teval e1 env
        val t2 = teval e2 env
      in
        case t1 of
          FunT(argsType, returnType) => 
            if(t2 = argsType) then 
              returnType 
            else 
              raise CallTypeMisM
          | _ => raise NotFunc
      end
    | List [] => ListT []
    | List l => ListT(map (fn (item) => teval item env) l)
    | Item(i, e1) => 
      let
        val t1 = teval e1 env
      in
        case t1 of
          ListT tlist => 
            let
              val lsize = length(tlist)
            in
              if(i > 0 andalso i <= lsize) then 
                List.nth(tlist, (i-1)) 
              else 
                raise ListOutOfRange
            end
        | _ => raise OpNonList
      end
    | Anon(argsType, argsName, e1) =>
      let
        val t1 = teval e1 ((argsName, argsType)::env)
      in
        FunT(argsType, t1)
      end
    | _ => raise UnknownType