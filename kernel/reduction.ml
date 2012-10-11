(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created under Benjamin Werner account by Bruno Barras to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Irreversibility of opacity by Bruno Barras *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Equal inductive types by Jacek Chrzaszcz as part of the module
   system, Aug 2002 *)

open Errors
open Util
open Names
open Term
open Univ
open Environ
open Closure
open Esubst

(* BEGIN PP *)
open Pp

let pr_id id = str (string_of_id id)

let print_sort = function
  | Prop Pos -> (str "Set")
  | Prop Null -> (str "Prop")
  | Type u -> (str "Type")

let pr_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let pr_name = function
  | Name id -> pr_id id
  | Anonymous -> str "_"

let pr_con sp = str(string_of_label(con_label sp))

let pr_rel_name e n =
  try let name, _, _= Environ.lookup_rel n e in pr_name name
  with Not_found -> str"UNBOUND"

let rec pr_constr h e c = if h < 0 then str"…" else match kind_of_term c with
  | Rel n -> pr_rel_name e n (*++str"("++int n++str")"*)
  | Meta n -> str "?m(" ++ int n ++ str ")"
  | Var id -> pr_id id
  | Sort s -> print_sort s
  | Cast (c,_, t) -> hov 1
      (str"(" ++ pr_constr (h-1) e c ++ cut() ++
       str":" ++ pr_constr (h-1) e t ++ str")")
  | Prod (Name(id) as n,t,c) -> hov 1
      (str"forall " ++ pr_id id ++ str":" ++ pr_constr (h-1) e t ++ str"," ++
       spc() ++ pr_constr (h-1) (Environ.push_rel (n,None,t) e) c)
  | Prod (Anonymous as n,t,c) -> hov 0
      (str"(" ++ pr_constr (h-1) e t ++ str " ->" ++ spc() ++
       pr_constr (h-1) (Environ.push_rel (n,None,t) e) c ++ str")")
  | Lambda (na,t,c) -> hov 1
      (str"(fun (" ++ pr_name na ++ str":" ++
       pr_constr (h-1) e t ++ str") =>" ++ spc() ++ pr_constr (h-1) (Environ.push_rel
       (na,None,t) e) c ++ str")")
  | LetIn (na,b,t,c) -> hov 0
      (str"let " ++ pr_name na ++ str":=" ++ pr_constr (h-1) e b ++
       str":" ++ brk(1,2) ++ pr_constr (h-1) e t ++ str" in " ++ cut() ++
       pr_constr (h-1) (Environ.push_rel (na,Some b,t) e) c)
  | App (c,l) ->  hov 1
      (str"(" ++ pr_constr (h-1) e c ++ spc() ++
       prlist_with_sep spc (pr_constr (h-1) e) (Array.to_list l) ++ str")")
  | Evar (e,l) -> hov 1
      (str"?e(" ++ int e ++ str")")
(*        str"{" ++ prlist_with_sep spc pr_constr (h-1) e (Array.to_list l) ++str"}") *)
  | Const c -> pr_con c
  | Ind (sp,i) -> let _, _, l = repr_mind sp in
      str(string_of_label l)++str"[" ++ int i ++ str"]"
  | Construct ((sp,i),j) -> let _, _, l = repr_mind sp in
      str(string_of_label l)++str"[" ++ int i ++ str "," ++ int j++ str"]"
  | Case (ci,p,c,bl) -> v 0
      (hv 0 (hov 0 (str"case " ++ pr_constr (h-1) e c ++spc()++
       str"return "++pr_constr (h-1) e p++spc()++str"with ")) ++ cut() ++
       prlist_with_sep (fun _ -> cut()) 
         (fun t -> str"| " ++ pr_constr (h-1) e t)
         (Array.to_list bl) ++
      cut() ++ str"end")
  | Fix ((t,i),(lna,tl,bl)) ->
(*       let fixl = Array.mapi (fun i na -> (na,t.(i),tl.(i),bl.(i))) lna in *)
      (* FIX env *)
      hov 1
        (str"fix " ++ int i ++ spc() (* ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,i,ty,bd) ->
           pr_name na ++ str"/" ++ int i ++ str":" ++ pr_constr (h-1) e ty ++
           cut() ++ str":=" ++ pr_constr (h-1) e bd) (Array.to_list fixl)) ++
         str"}"*))
  | CoFix(i,(lna,tl,bl)) ->
      (* FIX env *)
(*       let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in *)
      hov 1
        (str"cofix " ++ int i (* ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,ty,bd) ->
           pr_name na ++ str":" ++ pr_constr (h-1) e ty ++
           cut() ++ str":=" ++ pr_constr (h-1) e bd) (Array.to_list fixl)) ++
         str"}"*))
;;

let ppctx e = 
  let opt e = function None -> str "" | Some t -> str" := " ++ pr_constr 10 e t in
  string_of_ppcmds (hv 1 (List.fold_left (fun acc (id,ob,t) -> 
        pr_id id ++ opt e ob ++ str " : " ++ pr_constr 10 e t ++ spc() ++ acc)
      (str"") (Environ.named_context e)
      ++ str"---"++spc()++
      Environ.fold_rel_context (fun e (id,ob,t) acc -> acc ++ spc() ++
        pr_name id ++ opt e ob ++ str " : " ++ pr_constr 10 e t)
      e ~init:(str"")
      ))

let ppterm ?(depth=3) e x = string_of_ppcmds (pr_constr depth e x)

(* END PP *)

(* BEGIN TRACING INSTRUMENTATION *)

let debug = ref false
let indent = ref "";;
let times = ref [];;
let last_time = ref 0.0;;
(*D* let pp s = if !debug then Printf.eprintf "    %s%s\n" (String.make (String.length !indent) ' ') (Lazy.force s) *D*)
let __time () = (Unix.times ()).Unix.tms_utime
let __time () = Unix.gettimeofday ()
let __inside s =
 if !debug then begin
   let time1 = __time () in
   let c = s.[0] in
   times := time1 :: !times;
   Printf.eprintf "{{{ %s %s\n" !indent s;
   indent := !indent ^ String.make 1 c;
  end
;;
let __outside ?cmp_opt exc_opt =
 if !debug then
  begin
   let time2 = __time () in
   let time1 =
     match !times with time1::tl -> times := tl; time1 | [] -> assert false in
   let time = time2 -. time1 in
   last_time := time;
   Printf.eprintf "}}}\n    %s%s%s\n" (String.make (String.length !indent) ' ')
   (match exc_opt with
   | None ->   Printf.sprintf "returned in %.3f" time
   | Some e -> Printf.sprintf "failed in   %.3f (%s)" time
       (Printexc.to_string e))
   (match cmp_opt with
   | None -> ""
   | Some t when abs_float (t -. time) < 0.000001 -> ""
   | Some t ->
      Printf.sprintf " %s %.3f" (if t > time then "FASTER" else "SLOWER") t);
   try
    indent := String.sub !indent 0 (String.length !indent -1)
   with
    Invalid_argument _ -> indent := "??"; ()
  end
;;

(* END TRACING INSTRUMENTATION *)


let unfold_reference ((ids, csts), infos) k =
  match k with
    | VarKey id when not (Idpred.mem id ids) -> None
    | ConstKey cst when not (Cpred.mem cst csts) -> None
    | _ -> unfold_reference infos k

let rec is_empty_stack = function
    [] -> true
  | Zupdate _::s -> is_empty_stack s
  | Zshift _::s -> is_empty_stack s
  | _ -> false

(* Compute the lift to be performed on a term placed in a given stack *)
let el_stack el stk =
  let n =
    List.fold_left
      (fun i z ->
        match z with
            Zshift n -> i+n
          | _ -> i)
      0
      stk in
  el_shft n el

let compare_stack_shape stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> bal=0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zcase(c1,_,_)::s1, Zcase(c2,_,_)::s2) ->
        bal=0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        bal=0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | (_,_) -> false in
  compare_rec 0 stk1 stk2

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * fconstr * fconstr array
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (Array.map (fun t -> (l,t)) a) pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (Zcase(ci,p,br),(l,pstk)) ->
                (l,Zlcase(ci,l,p,br)::pstk)) in
  snd (pure_rec lfts stk)

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let whd_betaiota t =
  whd_val (create_clos_infos betaiota empty_env) (inject t)

let nf_betaiota t =
  norm_val (create_clos_infos betaiota empty_env) (inject t)

let whd_betaiotazeta x =
  match kind_of_term x with
    | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> x
    | _ -> whd_val (create_clos_infos betaiotazeta empty_env) (inject x)

let whd_betadeltaiota env t =
  match kind_of_term t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiota env) (inject t)

let whd_betadeltaiota_nolet env t =
  match kind_of_term t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiotanolet env) (inject t)

(* Beta *)

let beta_appvect c v =
  let rec stacklam env t stack =
    match kind_of_term t, stack with
        Lambda(_,_,c), arg::stacktl -> stacklam (arg::env) c stacktl
      | _ -> applist (substl env t, stack) in
  stacklam [] c (Array.to_list v)

let betazeta_appvect n c v =
  let rec stacklam n env t stack =
    if n = 0 then applist (substl env t, stack) else
    match kind_of_term t, stack with
        Lambda(_,_,c), arg::stacktl -> stacklam (n-1) (arg::env) c stacktl
      | LetIn(_,b,_,c), _ -> stacklam (n-1) (b::env) c stack
      | _ -> anomaly "Not enough lambda/let's" in
  stacklam n [] c (Array.to_list v)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)
type 'a conversion_function = env -> 'a -> 'a -> Univ.constraints
type 'a trans_conversion_function = transparent_state -> env -> 'a -> 'a -> Univ.constraints

exception NotConvertible
exception NotConvertibleVect of int

let compare_stacks f fmind lft1 stk1 lft2 stk2 cuniv =
  let rec cmp_rec pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          let cu1 = cmp_rec s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) -> Array.fold_right2 f a1 a2 cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec a1 a2 cu2
            | (Zlcase(ci1,l1,p1,br1),Zlcase(ci2,l2,p2,br2)) ->
                if not (fmind ci1.ci_ind ci2.ci_ind) then
		  raise NotConvertible;
		let cu2 = f (l1,p1) (l2,p2) cu1 in
                Array.fold_right2 (fun c1 c2 -> f (l1,c1) (l2,c2)) br1 br2 cu2
            | _ -> assert false)
      | _ -> cuniv in
  if compare_stack_shape stk1 stk2 then
    cmp_rec (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
  else raise NotConvertible

(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb = Mini_evd.conv_pb =
  | CONV
  | CUMUL

let sort_cmp pb s0 s1 cuniv =
  match (s0,s1) with
    | (Prop c1, Prop c2) when pb = CUMUL ->
        if c1 = Null or c2 = Pos then cuniv   (* Prop <= Set *)
        else raise NotConvertible
    | (Prop c1, Prop c2) ->
        if c1 = c2 then cuniv else raise NotConvertible
    | (Prop c1, Type u) when pb = CUMUL -> assert (is_univ_variable u); cuniv
    | (Type u1, Type u2) ->
	assert (is_univ_variable u2);
	(match pb with
           | CONV -> enforce_eq u1 u2 cuniv
	   | CUMUL -> enforce_leq u1 u2 cuniv)
    | (_, _) -> raise NotConvertible


let conv_sort env s0 s1 = sort_cmp CONV s0 s1 empty_constraint

let conv_sort_leq env s0 s1 = sort_cmp CUMUL s0 s1 empty_constraint

let rec no_arg_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_arg_available stk
  | Zshift _ :: stk -> no_arg_available stk
  | Zapp v :: stk -> Array.length v = 0 && no_arg_available stk
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_nth_arg_available n = function
  | [] -> true
  | Zupdate _ :: stk -> no_nth_arg_available n stk
  | Zshift _ :: stk -> no_nth_arg_available n stk
  | Zapp v :: stk ->
      let k = Array.length v in
      if n >= k then no_nth_arg_available (n-k) stk
      else false
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_case_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_case_available stk
  | Zshift _ :: stk -> no_case_available stk
  | Zapp _ :: stk -> no_case_available stk
  | Zcase _ :: _ -> false
  | Zfix _ :: _ -> true

let in_whnf (t,stk) =
  match fterm_of t with
    | (FLetIn _ | FCases _ | FApp _ | FCLOS _ | FLIFT _ | FCast _) -> false
    | FLambda _ -> no_arg_available stk
    | FConstruct _ -> no_case_available stk
    | FCoFix _ -> no_case_available stk
    | FFix(((ri,n),(_,_,_)),_) -> no_nth_arg_available ri.(n) stk
    | (FFlex _ | FProd _ | FEvar _ | FInd _ | FAtom _ | FRel _) -> true
    | FLOCKED -> assert false

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
(*D*   __inside "eqappr"; try let cmp_opt, __rc =  *D*)
  Util.check_for_interrupt ();
  (* First head reduce both terms *)
  let rec whd_both (t1,stk1) (t2,stk2) =
    let st1' = whd_stack (snd infos) t1 stk1 in
    let st2' = whd_stack (snd infos) t2 stk2 in
    (* Now, whd_stack on term2 might have modified st1 (due to sharing),
       and st1 might not be in whnf anymore. If so, we iterate ccnv. *)
    if in_whnf st1' then (st1',st2') else whd_both st1' st2' in
  try are_machines_eq lft1 lft2 st1 st2 cuniv
  with NotConvertible ->
  let ((hd1,v1),(hd2,v2)) = whd_both st1 st2 in
  let appr1 = (lft1,(hd1,v1)) and appr2 = (lft2,(hd2,v2)) in
  (* compute the lifts that apply to the head of the term (hd1 and hd2) *)
  let el1 = el_stack lft1 v1 in
  let el2 = el_stack lft2 v2 in
  (*D* let env = (env_of_infos (snd infos)) in *D*)
  (*D* pp(lazy("hd1="^ppterm env (term_of_lift_fconstr el1 hd1))); *D*)
  (*D* pp(lazy("hd2="^ppterm env (term_of_lift_fconstr el2 hd2))); *D*)
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
                    (*D* pp(lazy("(FAtom a1, FAtom a2)")); *D*)
	(match kind_of_term a1, kind_of_term a2 with
	   | (Sort s1, Sort s2) ->
	       if not (is_empty_stack v1 && is_empty_stack v2) then
		 anomaly "conversion was given ill-typed terms (Sort)";
	       sort_cmp cv_pb s1 s2 cuniv
	   | (Meta n, Meta m) ->
               if n=m
	       then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
	   | _ -> raise NotConvertible)
    | (FEvar ((ev1,args1),env1), FEvar ((ev2,args2),env2)) -> 
                    (*D* pp(lazy("(FEvar ((ev1,args1),env1), FEvar ((ev2,args2),env2))")); *D*)
        if ev1=ev2 then
          let u1 = convert_stacks l2r infos lft1 lft2 v1 v2 cuniv in
          convert_vect l2r infos el1 el2
            (Array.map (mk_clos env1) args1)
            (Array.map (mk_clos env2) args2) u1
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) -> 
                    (*D* pp(lazy("(FRel n, FRel m)")); *D*)
        if reloc_rel n el1 = reloc_rel m el2
        then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) -> 
                    (*D* pp(lazy("(FFlex fl1, FFlex fl2)")); *D*)
	(try (* try first intensional equality *)
	  if eq_table_key fl1 fl2
          then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          else raise NotConvertible
        with NotConvertible ->
          (* else the oracle tells which constant is to be expanded *)
          let (app1,app2) =
            (*D* let pr_unfold c l b = pp(lazy("unfold "^c^" =" ^ppterm ~depth:max_int env (term_of_lift_fconstr l b))) in *D*)
            if Conv_oracle.oracle_order l2r fl1 fl2 then
              match unfold_reference infos fl1 with
                | Some def1 -> 
                                (*D* pr_unfold "left" lft1 def1; *D*)
                                ((lft1, whd_stack (snd infos) def1 v1), appr2)
                | None ->
                    (match unfold_reference infos fl2 with
                      | Some def2 -> 
                                (*D* pr_unfold "right" lft2 def2; *D*)
                                      (appr1, (lft2, whd_stack (snd infos) def2 v2))
		      | None -> raise NotConvertible)
            else
	      match unfold_reference infos fl2 with
                | Some def2 -> 
                                (*D* pr_unfold "right" lft2 def2; *D*)
                                (appr1, (lft2, whd_stack (snd infos) def2 v2))
                | None ->
                    (match unfold_reference infos fl1 with
                    | Some def1 -> 
                                (*D* pr_unfold "left" lft1 def1; *D*)
                                    ((lft1, whd_stack (snd infos) def1 v1), appr2)
		    | None -> raise NotConvertible) in
          eqappr cv_pb l2r infos app1 app2 cuniv)

    (* other constructors *)
    | (FLambda _, FLambda _) -> 
                    (*D* pp(lazy("(FLambda _, FLambda _)")); *D*)
        (* Inconsistency: we tolerate that v1, v2 contain shift and update but
           we throw them away *)
        if not (is_empty_stack v1 && is_empty_stack v2) then
	  anomaly "conversion was given ill-typed terms (FLambda)";
        let (_,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        let u1 = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV l2r infos (el_lift el1) (el_lift el2) bd1 bd2 u1

    | (FProd (_,c1,c2), FProd (_,c'1,c'2)) -> 
                    (*D* pp(lazy("(FProd (_,c1,c2), FProd (_,c'1,c'2))")); *D*)
        if not (is_empty_stack v1 && is_empty_stack v2) then
	  anomaly "conversion was given ill-typed terms (FProd)";
	(* Luo's system *)
        let u1 = ccnv CONV l2r infos el1 el2 c1 c'1 cuniv in
        ccnv cv_pb l2r infos (el_lift el1) (el_lift el2) c2 c'2 u1

    (* Eta-expansion on the fly *)
    | (FLambda _, _) -> 
                    (*D* pp(lazy("(FLambda _, _)")); *D*)
        if v1 <> [] then
	  anomaly "conversion was given unreduced term (FLambda)";
        let (_,_ty1,bd1) = destFLambda mk_clos hd1 in
	eqappr CONV l2r infos
	  (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack v2)) cuniv
    | (_, FLambda _) -> 
                    (*D* pp(lazy("(_, FLambda _)")); *D*)
        if v2 <> [] then
	  anomaly "conversion was given unreduced term (FLambda)";
        let (_,_ty2,bd2) = destFLambda mk_clos hd2 in
	eqappr CONV l2r infos
	  (el_lift lft1, (hd1, eta_expand_stack v1)) (el_lift lft2, (bd2, [])) cuniv

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, _)      -> 
                    (*D* pp(lazy("(FFlex fl1, _)")); *D*)
        (match unfold_reference infos fl1 with
           | Some def1 ->
	       eqappr cv_pb l2r infos (lft1, whd_stack (snd infos) def1 v1) appr2 cuniv
           | None -> raise NotConvertible)
    | (_, FFlex fl2)      -> 
                    (*D* pp(lazy("(_, FFlex fl2)")); *D*)
        (match unfold_reference infos fl2 with
           | Some def2 ->
	       eqappr cv_pb l2r infos appr1 (lft2, whd_stack (snd infos) def2 v2) cuniv
           | None -> raise NotConvertible)

    (* Inductive types:  MutInd MutConstruct Fix Cofix *)

    | (FInd ind1, FInd ind2) -> 
                    (*D* pp(lazy("(FInd ind1, FInd ind2)")); *D*)
        if eq_ind ind1 ind2
	then
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | (FConstruct (ind1,j1), FConstruct (ind2,j2)) -> 
                    (*D* pp(lazy("(FConstruct (ind1,j1), FConstruct (ind2,j2))")); *D*)
	if j1 = j2 && eq_ind ind1 ind2
	then
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | (FFix ((op1,(_,tys1,cl1)),e1), FFix((op2,(_,tys2,cl2)),e2)) -> 
                    (*D* pp(lazy("(FFix ((op1,(_,tys1,cl1)),e1), FFix((op2,(_,tys2,cl2)),e2))")); *D*)
	if op1 = op2
	then
	  let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
	  let u1 = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let u2 =
            convert_vect l2r infos
	      (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 u1 in
          convert_stacks l2r infos lft1 lft2 v1 v2 u2
        else raise NotConvertible

    | (FCoFix ((op1,(_,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) -> 
                    (*D* pp(lazy("(FCoFix ((op1,(_,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2))")); *D*)
        if op1 = op2
        then
	  let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
          let u1 = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let u2 =
	    convert_vect l2r infos
	      (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 u1 in
          convert_stacks l2r infos lft1 lft2 v1 v2 u2
        else raise NotConvertible

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCases _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCases _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) -> assert false

     (* In all other cases, terms are not convertible *)
     | _ -> raise NotConvertible
(*D*   in __outside None; __rc with exn -> __outside (Some exn); raise exn  *D*)

and convert_stacks l2r infos lft1 lft2 stk1 stk2 cuniv =
(*D*   __inside "convert_stacks"; try let __rc =  *D*)
  compare_stacks
    (fun (l1,t1) (l2,t2) c -> ccnv CONV l2r infos l1 l2 t1 t2 c)
    (eq_ind)
    lft1 stk1 lft2 stk2 cuniv
(*D*   in __outside None; __rc with exn -> __outside (Some exn); raise exn  *D*)

and convert_vect l2r infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if lv1 = lv2
  then
    let rec fold n univ =
      if n >= lv1 then univ
      else
        let u1 = ccnv CONV l2r infos lft1 lft2 v1.(n) v2.(n) univ in
        fold (n+1) u1 in
    fold 0 cuniv
  else raise NotConvertible

and are_machines_eq l1 l2 (hd1,st1) (hd2,st2) u =
(*D*   __inside "are_machines_eq"; try let __rc =  *D*)
  are_stacks_eq l1 l2 st1 st2 (are_fterms_eq l1 l2 hd1 hd2 u)
(*D*   in __outside None; __rc with exn -> __outside (Some exn); raise exn  *D*)

and are_stacks_eq lft1 lft2 stk1 stk2 u =
  compare_stacks
    (fun (l1,t1) (l2,t2) c -> are_fterms_eq l1 l2 t1 t2 c)
    (eq_ind)
    lft1 stk1 lft2 stk2 u

and are_subs_eq u = function
  | ESID i, ESID j -> if i=j then u else raise NotConvertible
  | CONS (a1, s1), CONS (a2, s2) ->
      (try are_subs_eq (Array.fold_right2 (fun f1 f2 u -> 
             are_fterms_eq el_id el_id f1 f2 u) a1 a2 u) (s1,s2)
      with Invalid_argument _ -> raise NotConvertible)
  | SHIFT(i,s1), SHIFT(j,s2)
  | LIFT(i,s1), LIFT(j,s2) ->
      if i=j then are_subs_eq u (s1,s2) else raise NotConvertible
  | _ -> raise NotConvertible

and are_fterms_eq l1 l2 hd1 hd2 u = 
  match (fterm_of hd1, fterm_of hd2) with
    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
          if eq_table_key fl1 fl2 then u
          else raise NotConvertible
    | (FCLOS(t1, e1), FCLOS(t2,e2)) ->
          if eq_constr t1 t2 && l1 = l2 then are_subs_eq u (e1, e2)
          else raise NotConvertible
    (* In all other cases, terms are not convertible *)
    | _ -> raise NotConvertible

let clos_fconv trans cv_pb l2r evars env t1 t2 =
(*D*   __inside "fconv"; try let __rc =  *D*)
(*D*  pp(lazy(ppctx env  ^ "\n----------------------------\n"));  *D*)
(*D*  pp(lazy(ppterm ~depth:max_int env t1 ^ " \n= " ^ ppterm ~depth:max_int env t2));  *D*)
  let infos = trans, create_clos_infos ~evars betaiotazeta env in
  ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) empty_constraint
(*D*   in __outside None; __rc with exn -> __outside (Some exn); raise exn  *D*)

type cpb = 
  (string * int * int) * (Names.Idpred.t * Names.Cpred.t) * conv_pb * bool *
   Mini_evd.EvarMap.t * Environ.env *
   Term.constr * Term.constr * Univ.constraints option

let loc_x, loc_y = ref 0, ref 0
let filename = ref ""

let print_cpb ((s,i,j),_,_,_,_,_,_,_,b) =
  Printf.sprintf "%S , %d , %d , %b , " s i j (b <> None)

let todump, dumping = ref ([] : cpb list), ref false

let load_dump s =
  let ic = open_in_bin s in
  try (Marshal.from_channel ic : cpb list)
  with End_of_file -> (prerr_endline ("Unable to load " ^ s)); []

let set_dump_loc (x,y) = loc_x := x; loc_y := y

let set_dump_cpbs s =
  filename :=
    String.concat Filename.dir_sep 
      (Util.List.lastn 3 (Str.split (Str.regexp Filename.dir_sep) s));
  let oc = open_out_bin s in
  dumping := true;
  at_exit (fun () ->
    begin
      try Marshal.to_channel oc !todump [Marshal.Closures]
      with Invalid_argument _ -> prerr_endline ("Unable to marshal "^s)
    end;
    close_out oc)

let dump reds cv_pb l2r evars env t1 t2 time rc =
  if !dumping && time > 0.0004 then
    todump :=
      ((!filename,!loc_x,!loc_y), reds, cv_pb, l2r,
      evars, env, t1, t2, rc) :: !todump

let trans_fconv reds cv_pb l2r evars env t1 t2 time =
  try
    if eq_constr t1 t2 then empty_constraint
    else 
      let rc = clos_fconv reds cv_pb l2r evars env t1 t2 in
      time := (Unix.times ()).Unix.tms_utime -. !time;
      dump reds cv_pb l2r evars env t1 t2 !time (Some rc);
      rc
  with e ->
    time := (Unix.times ()).Unix.tms_utime -. !time;
    dump reds cv_pb l2r evars env t1 t2 !time None;
    raise e

let run_cpb (_,reds, cv_pb, l2r, evars, env, t1, t2, rc) =
  let time = ref (Unix.times ()).Unix.tms_utime in
  try
    let u = trans_fconv reds cv_pb l2r evars env t1 t2 time in
    match rc with
    | None -> !time, false
    | Some rc -> !time, Univ.compare_constraints rc u
  with e -> !time, None = rc

let trans_fconv reds cv_pb l2r evars env t1 t2 =
  let time = ref (Unix.times ()).Unix.tms_utime in
  trans_fconv reds cv_pb l2r evars env t1 t2 time

let trans_conv_cmp ?(l2r=false) conv reds = trans_fconv reds conv l2r Mini_evd.EvarMap.empty
let trans_conv ?(l2r=false) ?(evars=Mini_evd.EvarMap.empty) reds = trans_fconv reds CONV l2r evars
let trans_conv_leq ?(l2r=false) ?(evars=Mini_evd.EvarMap.empty) reds = trans_fconv reds CUMUL l2r evars

let fconv = trans_fconv (Idpred.full, Cpred.full)

let conv_cmp ?(l2r=false) cv_pb = fconv cv_pb l2r Mini_evd.EvarMap.empty
let conv ?(l2r=false) ?(evars=Mini_evd.EvarMap.empty) = fconv CONV l2r evars
let conv_leq ?(l2r=false) ?(evars=Mini_evd.EvarMap.empty) = fconv CUMUL l2r evars

let conv_leq_vecti ?(l2r=false) ?(evars=Mini_evd.EvarMap.empty) env v1 v2 =
  Array.fold_left2_i
    (fun i c t1 t2 ->
      let c' =
        try conv_leq ~l2r ~evars env t1 t2
        with NotConvertible -> raise (NotConvertibleVect i) in
      union_constraints c c')
    empty_constraint
    v1
    v2

(* option for conversion *)

let vm_conv = ref (fun cv_pb -> fconv cv_pb false Mini_evd.EvarMap.empty)
let set_vm_conv f = vm_conv := f
let vm_conv cv_pb env t1 t2 =
  try
    !vm_conv cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
      (* If compilation fails, fall-back to closure conversion *)
      fconv cv_pb false Mini_evd.EvarMap.empty env t1 t2


let default_conv =
  ref (fun cv_pb ?(l2r=false) -> fconv cv_pb l2r Mini_evd.EvarMap.empty)

let set_default_conv f = default_conv := f

let default_conv cv_pb ?(l2r=false) env t1 t2 =
  try
    !default_conv ~l2r cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
      (* If compilation fails, fall-back to closure conversion *)
      fconv cv_pb false Mini_evd.EvarMap.empty env t1 t2

let default_conv_leq = default_conv CUMUL
(*
let convleqkey = Profile.declare_profile "Kernel_reduction.conv_leq";;
let conv_leq env t1 t2 =
  Profile.profile4 convleqkey conv_leq env t1 t2;;

let convkey = Profile.declare_profile "Kernel_reduction.conv";;
let conv env t1 t2 =
  Profile.profile4 convleqkey conv env t1 t2;;
*)

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env t n =
  match kind_of_term (whd_betadeltaiota env t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_applist env t nl =
  List.fold_left (hnf_prod_app env) t nl

(* Dealing with arities *)

let dest_prod env =
  let rec decrec env m c =
    let t = whd_betadeltaiota env c in
    match kind_of_term t with
      | Prod (n,a,c0) ->
          let d = (n,None,a) in
	  decrec (push_rel d env) (add_rel_decl d m) c0
      | _ -> m,t
  in
  decrec env empty_rel_context

(* The same but preserving lets *)
let dest_prod_assum env =
  let rec prodec_rec env l ty =
    let rty = whd_betadeltaiota_nolet env ty in
    match kind_of_term rty with
    | Prod (x,t,c)  ->
        let d = (x,None,t) in
	prodec_rec (push_rel d env) (add_rel_decl d l) c
    | LetIn (x,b,t,c) ->
        let d = (x,Some b,t) in
	prodec_rec (push_rel d env) (add_rel_decl d l) c
    | Cast (c,_,_)    -> prodec_rec env l c
    | _               -> l,rty
  in
  prodec_rec env empty_rel_context

exception NotArity

let dest_arity env c =
  let l, c = dest_prod_assum env c in
  match kind_of_term c with
    | Sort s -> l,s
    | _ -> raise NotArity

let is_arity env c =
  try
    let _ = dest_arity env c in
    true
  with NotArity -> false
