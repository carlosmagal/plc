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
    | Prim1(ope, expr1) =>
      let
        val type1 = teval expr1 env
      in
        case ope of
          ("!") => if(type1 = BoolT) then BoolT else raise UnknownType
        | ("-") => if(type1 = IntT) then IntT else raise UnknownType
        | ("hd") => 
          let in
            case expr1 of
              ESeq(SeqT(t)) => raise EmptySeq
            | _ => 
              let in
                case type1 of
                  SeqT(t) => t
                | _ => raise UnknownType
              end
          end
        | ("tl") => 
          let in
            case expr1 of
              ESeq(SeqT(t)) => raise EmptySeq
            | _ => 
              let in
                case type1 of
                  SeqT(t) => SeqT(t)
                | _ => raise UnknownType
              end
          end
        | ("ise") => 
          let in
            case type1 of
              SeqT(t) => BoolT
            | _ => raise UnknownType
          end
        | ("print") => ListT([])
        | _ => raise UnknownType
      end
    | Prim2(operator, expr1, expr2) =>
      let
        val type1 = teval expr1 env
        val type2 = teval expr2 env
      in
        case operator of
           ("*") => if (type1 = type2 andalso type1 = IntT) then IntT else raise UnknownType
          | ("/") => if (type1 = type2 andalso type1 = IntT) then IntT else raise UnknownType
          | ("+") => if (type1 = type2 andalso type1 = IntT) then IntT else raise UnknownType
          | ("-") => if (type1 = type2 andalso type1 = IntT) then IntT else raise UnknownType
          | (";") => type2
          | ("&&") => if (type1 = type2) then BoolT else raise UnknownType
          | ("::") => if (type2 = SeqT(type1)) then SeqT(type1) else raise UnknownType
          | ("<") => if (type1 = type2 andalso type1 = IntT) then BoolT else raise UnknownType
          | ("<=") => if (type1 = type2 andalso type1 = IntT) then BoolT else raise UnknownType
          | ("=") => if (type1 <> type2) then raise NotEqTypes else
            let in
              case type1 of
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
              | ListT(typeList) => 
                let
                  val list = map(fn(t) => 
                      case t of
                        BoolT => BoolT
                      | IntT => IntT
                      | ListT([]) => ListT([])
                      | _ => raise NotEqTypes) 
                    typeList
                in
                  BoolT
                end
              | _ => raise UnknownType
            end
          | ("!=") => if(type1 <> type2) then raise NotEqTypes else
            let in
              case type1 of
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
              | ListT(typeList) => 
                let
                  val list = map(fn(t) => 
                      case t of
                        BoolT => BoolT
                      | IntT => IntT
                      | ListT([]) => ListT([])
                      | _ => raise NotEqTypes) 
                    typeList
                in
                  BoolT
                end
              | _ => raise UnknownType
            end
        | _ => raise UnknownType
      end
    | If(expr1, expr2, expr3) =>
      let
        val type1 = teval expr1 env
        val type2 = teval expr2 env
        val type3 = teval expr3 env
      in
        if(type1 <> BoolT) then 
          raise IfCondNotBool 
        else 
          if(type2 <> type3) then 
            raise DiffBrTypes 
          else 
            type3
      end
    | Match (expr, matchExpr) => 
      if(matchExpr = []) then 
        raise NoMatchResults 
      else 
        let
          val exprType = teval expr env
          val equalCondResultTypes = fn (condExpr, resultExpr) => ( 
            case condExpr of
              NONE => teval resultExpr env
            | SOME(e) => 
              let
                val condType = teval e env
              in
                if (condType = exprType) then teval resultExpr env else raise MatchCondTypesDiff
              end
          )
          val resultTypesList = map equalCondResultTypes matchExpr
          val resultType1 = hd(resultTypesList)
          val equalType = fn (item) => if(item = resultType1) then true else raise MatchResTypeDiff
          val filteredList = List.filter equalType resultTypesList
        in
          resultType1
        end
    | Call(expr1, expr2) =>
      let
        val type1 = teval expr1 env
        val type2 = teval expr2 env
      in
        case type1 of
          FunT(argsType, returnType) => 
            if(type2 = argsType) then returnType else raise CallTypeMisM
          | _ => raise NotFunc
      end
    | List [] => ListT []
    | List l => ListT(map (fn (item) => teval item env) l)
    | Item(i, expr1) => 
      let
        val type1 = teval expr1 env
      in
        case type1 of
          ListT(typeList) => 
            let
              val listSize = length(typeList)
            in
              if(i > 0 andalso i <= listSize) then List.nth(typeList, (i-1)) else raise ListOutOfRange
            end
        | _ => raise OpNonList
      end
    | Anon(argsType, argsName, expr1) =>
      let
        val type1 = teval expr1 ((argsName, argsType)::env)
      in
        FunT(argsType, type1)
      end
    | _ => raise UnknownType