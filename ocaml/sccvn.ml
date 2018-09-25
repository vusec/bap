(** Strongly connected component based value numbering.

    Currently we only implement the RPO algorithm, described in
    "SCC-Based Value Numbering" by Keith Cooper and Taylor Simpson.
    http://citeseer.ist.psu.edu/41805.html

    TODO: This has been hacked on a bit and could use some cleanup. (Removing
    silly things and making it easier to understand.)

    TODO: canonicalize constants in HInt

    @author Ivan Jager
*)

(* Big picture:

   vn_h maps vars to their value numbers (VN). Vars which map to the same
   VN are belived to be congruent. Everything starts off at T, except
   free variables which are assumed to be unique.

   The [lookup] function tries to find a matching (same operator and
   congruent operants) expression in a hashtable (eid2vn). If none is present
   it adds the expression with a new VN, thereby creating a new equivalence
   class.

   The RPO algorithm works by calling [lookup] for each variable, updating
   vn_h with the new VN, until it reaches a fixed point. At this point,
   if two variables have the same VN, they are equivalent.

   The latice looks like this: Top -> HInt (constant) -> Hash (variable, corresponds to bottom in the CP lattice)

*)


open Big_int_Z
open Big_int_convenience
open Type
open Ssa
open BatListFull
open Arithmetic

module VH = Var.VarHash
module C = Cfg.SSA
module G = C.G

module D = Debug.Make(struct let name = "SCCVN" and default=`NoDebug end)
open D

module Dom = Dominator.Make(G)

type vn = Top | Hash of Ssa.var | HInt of (big_int * typ)
let top = Top
type expid =
  | Const of Ssa.value (* Except Var *)
  | It of vn * vn * vn
  | Ex of big_int * big_int * vn
  | Con of vn * vn
  | Bin of binop_type * vn * vn
  | Un of unop_type * vn
  | Cst of cast_type * typ * vn
  | Unique of var (* for free variables and unknowns *)
  | Ld of vn * vn * vn * typ
  | St of vn * vn * vn * vn * typ
  | Ph of vn list

let vn_compare vn1 vn2 = match vn1,vn2 with
  | Top,Top -> 0
  | Hash(v1), Hash(v2) -> compare v1 v2
  | HInt(i1,t1), HInt(i2,t2) ->
      let c1 = compare t1 t2 in
      if c1 <> 0 then c1
      else compare_big_int i1 i2
  | _, _ ->
    let getnum = function
      | Top -> 0 | Hash _ -> 1 | HInt _ -> 2
    in
    compare (getnum vn1) (getnum vn2)

let vn_eq vn1 vn2 = (vn_compare vn1 vn2) = 0

let (==!) = vn_eq
let (<=!) vn1 vn2 = vn_compare vn1 vn2 <= 0
let (<>!) v1 v2 = not (vn_eq v1 v2)

let expid_eq e1 e2 =
  (* values, vns, bops, uops, types, cts, vars, big ints *)
  let getnum = function
    | Const _ -> 1
    | It _ -> 2
    | Ex _ -> 3
    | Con _ -> 4
    | Bin _ -> 5
    | Un _ -> 6
    | Cst _ -> 7
    | Unique _ -> 8
    | Ld _ -> 9
    | St _ -> 10
    | Ph _ -> 11
  in
  let getargs = function
    | Const(v) -> [v], [], [], [], [], [], [], []
    | It(vn1,vn2,vn3) -> [], [vn1;vn2;vn3], [], [], [], [], [], []
    | Ex(bi1,bi2,vn1) -> [], [vn1], [], [], [], [], [], [bi1;bi2]
    | Con(vn1,vn2) -> [], [vn1;vn2], [], [], [], [], [], []
    | Bin(bop, vn1, vn2) -> [], [vn1; vn2], [bop], [], [], [], [], []
    | Un(uop, vn) -> [], [vn], [], [uop], [], [], [], []
    | Cst(ct, t, vn) -> [], [vn], [], [], [t], [ct], [], []
    | Unique(var) -> [], [], [], [], [], [], [var], []
    | Ld(vn1, vn2, vn3, t) -> [], [vn1; vn2; vn3], [], [], [t], [], [], []
    | St(vn1, vn2, vn3, vn4, t) -> [], [vn1; vn2; vn3; vn4], [], [], [t], [], [], []
    | Ph(vnlist) -> [], vnlist, [], [], [], [], [], []
  in
  if (getnum e1) <> (getnum e2) then false
  else (
    let l1,l2,l3,l4,l5,l6,l7,l8 = getargs e1 in
    let r1,r2,r3,r4,r5,r6,r7,r8 = getargs e2 in
    let phil = (List.length l2) == (List.length r2) in
    let b1 = List.for_all2 (==) l1 r1 in
    let b2 = if phil then List.for_all2 (==) l2 r2 else false in
    let b3 = List.for_all2 (=) l3 r3 in
    let b4 = List.for_all2 (=) l4 r4 in
    let b5 = List.for_all2 (=) l5 r5 in
    let b6 = List.for_all2 (=) l6 r6 in
    let b7 = List.for_all2 (=) l7 r7 in
    let b8 = List.for_all2 (==%) l8 r8 in
    if b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 then
      true
    else if b3 & b4 & b5 & b6 & b7 & b8 then
      (* e1 and e2 are not physically equal.  But maybe the
         subexpressions are structurally, but not physically,
         equal. *)
      List.for_all2 Ssa.full_value_eq l1 r1
      && if phil then List.for_all2 vn_eq l2 r2 else false
    else
      false)

module EH =
  Hashtbl.Make(struct
                 type t = expid
                 let equal = expid_eq
                 and hash = Hashtbl.hash
               end)

type rpoinfo = { (* private to the SCCVN module *)
  vn_h : vn VH.t; (* maps vars to value numbers *)
  eid2vn : vn EH.t; (* maps expids to value numbers *)
  vn2eid : expid VH.t; (* inverse of eid2vn *)
  (* vn2eid is expid VH.t rather than (vn, expid) Hashtbl.t, since top is
     never used as a key, and the map from HInt is trivial. *)
  vn2prepends : Var.t VH.t;
  (*
   * vn2prepends collects all the vns that our optimizer synthesized, indexed
   * by the avar of the statement to which they should be prepended.
   *)
}

let do_vn2eid find = function
  | Top ->
    dprintf "do_vn2eid: Not_found";
    raise Not_found
  | HInt(i,t) -> Const(Int(i,t))
  | Hash v -> find v

let vn2eid info = do_vn2eid (VH.find info.vn2eid)

let vn2eid_option info vn =
  try
    Some (vn2eid info vn)
  with Not_found -> None

let vntyp = function
  | Top -> raise Not_found
  | HInt (_, typ) -> typ
  | Hash v -> Var.typ v

let hash_to_string = function
  | Top -> "T"
  | Hash v -> "<"^Pp.var_to_string v^">"
  | HInt(i,t) -> string_of_big_int i ^":"^ Pp.typ_to_string t

let eid_to_str = function
  | Const v -> Printf.sprintf "Const (%s)" (Pp.value_to_string v)
  | It _ -> "It"
  | Ex _ -> "Ex"
  | Con _ -> "Con"
  | Bin (op, vn1, vn2) ->
    Printf.sprintf "Bin (%s, %s, %s)" (Pp.binop_to_string op)
      (hash_to_string vn1) (hash_to_string vn2)
  | Un (op, vn) ->
    Printf.sprintf "Un (%s, %s)" (Pp.unop_to_string op)
                     (hash_to_string vn)
  | Cst _ -> "Cst"
  | Unique var -> Printf.sprintf "Unique (%s)" (Pp.var_to_string var)
  | Ld _ -> "Ld"
  | St _ -> "St"
  | Ph vns ->
    List.fold_left (fun acc vn ->
        Printf.sprintf "%s %s," acc (hash_to_string vn)) "Ph" vns

let join a b = match (a,b) with
  | (Top, x)
  | (x, Top) ->
      Some Top
  | _, _ when a ==! b ->
      Some a
  (* | (HInt _, HInt _) when a ==% b -> *)
  (*     Some a *)
  (* | (Hash x, Hash y) when x == y -> *)
  (*     Some a *)
  | (Hash _, Hash _)
  | (HInt _, HInt _) ->
      None
  | ((Hash _), _)
  | (_, (Hash _)) ->
      None (* A hash and a constant can not be simplified *)

let meet a b = match (a,b) with
  | (Top, x)
  | (x, Top) ->
      Some x
  | _, _ when a ==! b ->
      Some a
  (* | (HInt _, HInt _) when a ==% b -> *)
  (*     Some a *)
  (* | (Hash x, Hash y) when x == y -> *)
  (*     Some a *)
  | (Hash _, Hash _)
  | (HInt _, HInt _) ->
      None
  | ((Hash _), _)
  | (_, (Hash _)) ->
      None (* A hash and a constant can not be simplified *)


(** [node_sdom cfg a b] returns true if position [a] strictly dominates
    position [b]. (where a position is a bbid * distance into the BB) *)
let pos_sdom cfg =
  let {Dom.sdom=sdom;} = Dom.compute_all cfg (G.V.create Cfg.BB_Entry) in
  (fun (a_bb, a_i) (b_bb, b_i) ->
     sdom a_bb b_bb || (a_bb = b_bb && a_i < b_i)
  )



let defsite cfg =
  let defsites = VH.create 5700 in
  G.iter_vertex
    (fun b ->
       let rec addone i = function
         | Move(l,_,_) -> VH.add defsites l (b,i)
         | _ -> ()
         in
       List.iteri addone (C.get_stmts cfg b)
    )
    cfg;
  let beforeentry = (C.G.V.create Cfg.BB_Entry, -1) in
  (fun x ->
     try VH.find defsites x
     with Not_found -> beforeentry (* globals come from before BB_Entry *)
  )


let add_const =
  let name = "fake var for constant"
  and typ = Array(TMem Ast.reg_1, TMem Ast.reg_1) (* BS type *) in
  (fun info c ->
     let eid = Const c in
     let h = match c with
       | Int(i,t) ->
           HInt(i,t)
       | _ ->
           let v = Var.newvar name typ in
           VH.add info.vn2eid v eid;
           Hash v
     in
     EH.add info.eid2vn eid h;
     h )

let get_expid info =
  let vn = function
    | (Int _ | Lab _) as v -> (
        try EH.find info.eid2vn (Const v)
        with Not_found ->
          add_const info v
      )
    | Var x -> (
        try VH.find info.vn_h x
        with Not_found ->
          failwith("get_expid: unknown var: "^Pp.var_to_string x)
      )
  in
  fun var -> function
    | Val(Var _ as v) ->
        vn2eid info (vn v)
    | Val v -> Const v
    | Ite(c,v1,v2) -> It(vn c, vn v1, vn v2)
    | Extract(h,l,e) -> Ex(h,l, vn e)
    | Concat(le,re) -> Con(vn le, vn re)
    | BinOp((PLUS|TIMES|AND|OR|XOR|EQ|NEQ) as op,v1,v2) ->
        let (h1,h2) = (vn v1, vn v2) in
        if h1 <=! h2 then Bin(op, h1, h2) else Bin(op, h2, h1)
    | BinOp(op,v1,v2) -> Bin(op, vn v1, vn v2)
    | UnOp(op, v) -> Un(op, vn v)
    | Cast(ct, t, v) -> Cst(ct,t, vn v)
    | Unknown _ -> Unique var
    | Load(m,i,e,t) -> Ld(vn m, vn i, vn e, t)
    | Store(m,i,v,e,t) -> St(vn m, vn i, vn v, vn e, t)
    | Phi vars -> Ph(List.map (fun v -> vn (Var v)) vars)

(*
 * We collect all the add or sub operations in the eid tree, until
 * we reach a leaf or a non add/sub operation (we also handle the unary
 * minus). Notice that any add/sub operations that appear lower in the
 * tree (beneath a non add/sub op) have already been normalized at an
 * earlier point.
 * We record all operands in this record (folding constants as they're
 * collected).
 *)
type addsubnorm_ctx = {
  plusvars : Var.t list;
  minusvars : Var.t list;
  constant : (Big_int_Z.big_int * Type.typ) option;
}

let addsub_ctx_to_str ctx =
  let pv = List.fold_left (fun acc v ->
      Printf.sprintf "%s, %s" acc (Pp.var_to_string v)) "" ctx.plusvars in
  let mv = List.fold_left (fun acc v ->
      Printf.sprintf "%s, %s" acc (Pp.var_to_string v)) "" ctx.minusvars in
  let cst = match ctx.constant with
    | None -> "_"
    | Some (i, t) ->
      Printf.sprintf "(%s, %s)" (Big_int_Z.string_of_big_int i) (Pp.typ_to_string t)
  in
  Printf.sprintf "+(%s) - (%s) + %s" pv mv cst

let join_ctx ctx1 ctx2 =
  match ctx1, ctx2 with
  | None, None
  | Some _, None
  | None, Some _ ->
    None
  | Some ctx1, Some ctx2 ->
    begin
      let open Big_int_convenience in
      let constant = match ctx1.constant, ctx2.constant with
        | None, None -> None
        | Some constant, None
        | None, Some constant -> Some constant
        | Some (i1, t1), Some (i2, t2) ->
          if t1 <> t2 then begin
            let s = Printf.sprintf "Constant types differ: %s vs %s"
              (Pp.typ_to_string t1) (Pp.typ_to_string t2) in
            failwith s
          end;
          Some (Arithmetic.binop Type.PLUS (i1, t1) (i2, t2))
      in
      Some {
        plusvars = ctx1.plusvars @ ctx2.plusvars;
        minusvars = ctx1.minusvars @ ctx2.minusvars;
        constant;
      }
    end

let optctx_add_var ~sign_is_plus ctx var =
  match sign_is_plus with
  | true -> {ctx with plusvars = var :: ctx.plusvars}
  | false -> {ctx with minusvars = var :: ctx.minusvars}

let collect_leaves info eid =
  let rec do_operand ~sign_is_plus ctx x =
    match x with
    | HInt cst ->
      dprintf "do_operand: HInt %s" (Big_int_Z.string_of_big_int (fst cst));
      begin
        let cst = match sign_is_plus with
          | true -> cst
          | false -> Arithmetic.unop Type.NEG cst
        in
        let constant = match ctx.constant with
          | None -> Some cst
          | Some ocst -> Some (Arithmetic.binop Type.PLUS cst ocst)
        in
        Some {ctx with constant}
      end
    | Hash var as vn ->
      dprintf "do_operand: Hash %s" (Pp.var_to_string var);
      begin
        match vn2eid_option info vn with
        | None ->
          Some (optctx_add_var ~sign_is_plus ctx var)
        | Some inner_eid ->
          do_eid ~sign_is_plus ~upvar:var ctx inner_eid
      end
    | Top ->
      dprintf "do_operand: giving up because of Top";
      None
  and do_eid ~sign_is_plus ?upvar ctx eid =
    dprintf "do_eid: %s" (eid_to_str eid);
    match eid with
    | Bin (Type.PLUS, a, b) ->
      join_ctx (do_operand ~sign_is_plus ctx a) (do_operand ~sign_is_plus ctx b)
    | Bin (Type.MINUS, a, b) ->
      join_ctx (do_operand ~sign_is_plus ctx a)
        (do_operand ~sign_is_plus:(not sign_is_plus) ctx b)
    | Un (Type.NEG, a) ->
      do_operand ~sign_is_plus:(not sign_is_plus) ctx a
    | Unique var ->
      Some (optctx_add_var ~sign_is_plus ctx var)
    | _ ->
      (*
       * In any other case, normalize the expressions up to the first
       * non-additive leaf.
       *)
      begin
        match upvar with
        | None ->
          failwith "Our toplevel eid was a load, why are we even here?"
        | Some upvar ->
          Some (optctx_add_var ~sign_is_plus ctx upvar)
      end
  in
  let constant = None in
  let empty_ctx = {plusvars = []; minusvars = []; constant} in
  dprintf "collect_leaves: starting from %s" (eid_to_str eid);
  do_eid ~sign_is_plus:true empty_ctx eid

(*
 * Normalize the addsubctx by
 * a) Canceling out appearences of the same value in plus- and minus- vars
 * b) Sorting the vars so that they always appear in the same order for
 *    equivalent expressions.
 *)
let simplify_addsubctx ctx =
  let eliminate_opposites vars1 vars2 =
    let matchit el vars =
      let rec inner acc rest =
        match rest with
        | [] ->
          None
        | h :: rest ->
          if Var.compare h el = 0 then
            Some ((List.rev acc) @ rest)
          else
            inner (h :: acc) rest
      in
      inner [] vars
    in
    let rec multidiff acc1 rem1 vars2 =
      match rem1 with
      | [] ->
        (acc1, vars2)
      | el :: rest ->
        begin
          match matchit el vars2 with
          | None ->
            (* Nothing to cancel el with in vars2, keep it *)
            multidiff (el :: acc1) rest vars2
          | Some vars2 ->
            (* Canceled el, drop it from both sides *)
            multidiff acc1 rest vars2
        end
    in
    let vars1, vars2 = multidiff [] vars1 vars2 in
    let vars2, vars1 = multidiff [] vars2 vars1 in
    (vars1, vars2)
  in
  let plusvars, minusvars = eliminate_opposites ctx.plusvars ctx.minusvars in
  (* Normalization, should be useful for the eid we do generate *)
  let plusvars = List.sort Var.compare plusvars in
  let minusvars = List.sort Var.compare minusvars in
  {ctx with plusvars; minusvars}

(*
 * Normally SCCVN works with values calculated in the input program. However,
 * our optimizer will synthesize values during normalization (e.g. converting
 * [c = a - b] -> [tmp = - b; c = a + tmp]). This function updates our tables
 * so that it appears that those values are available. Later, we need to also
 * emit ssa statements which define those values prior to their use.
 *)
let register_eid info eid typ =
  dprintf "register_eid: in";
  let newvar = Var.newvar "sccvn_norm" in
  let var = newvar typ in
  let vn = Hash var in
  try
    EH.find info.eid2vn eid
  with Not_found ->
    begin
      dprintf "registering var %s for eid %s" (Pp.var_to_string var) (eid_to_str eid);
      VH.add info.vn_h var vn;
      EH.add info.eid2vn eid vn;
      VH.add info.vn2eid var eid;
      vn
    end

let neg_var info v =
  let eid = Un (Type.NEG, (Hash v)) in
  register_eid info eid (Var.typ v)

(*
 * Given a (hopefully normalized) addsubctx, build up an eid tree and
 * return the root.
 * The eid tree has the form:
 *
 * +-----+    +-----+        +-----+        +-----+
 * |  +  | -> |  +  | -> ... |  +  | -  ... |  +  |
 * +-----+    +-----+        +-----+        +-----+
 *    |          |              |              |
 * +----+     +----+         +-----+        +-----+
 * | v1 |     | v2 |         |  -  |        | cst |
 * +----+     +----+         +-----+        +-----+
 *                              |
 *                           +----+
 *                           | v3 |
 *                           +----+
 * where v1, v2 are plusvars, v3 is a minusvar and cst is the result of
 * folding all the constants. If there are no plusvars, our tree stars
 * with the negation of the first minusvar as an operand. The constant
 * is omitted if zero.
 *)
let addsubctx2eid info ctx =
  let vns_of_minusvars ~minusvars =
    let wrap = neg_var info in
    List.map wrap minusvars
  in
  let vns_of_plusvars ~plusvars =
    let wrap v =
      Hash v
    in
    List.map wrap plusvars
  in
  let rec do_vars_rest vns cst =
    match vns with
    | [] ->
      begin
        match cst with
        | None ->
          (*
           * We can still end up here e.g. for (x + y) - x -> y, as y
           * becomes the first_var and there is no constant action. Pretend
           * it was zero, our caller should optimize it away. The type
           * will not be looked at.
           *)
          HInt (Big_int_convenience.bi0, Type.Reg 32)
        | Some cst ->
          HInt cst
      end
    | [vn] ->
      dprintf "do_vars_rest [vn]";
      begin
        (* OK, reached the last var, now see if we have a constant to add *)
        match cst with
        | None ->
          vn
        | Some (i, _) when Big_int_convenience.bi_is_zero i ->
          vn
        | Some cst ->
          let eid = Bin (Type.PLUS, vn, HInt cst) in
          register_eid info eid (vntyp vn)
      end
    | vn :: rest ->
      dprintf "do_vars_rest vn :: rest";
      begin
        let vn_rest = do_vars_rest rest cst in
        let eid = Bin (Type.PLUS, vn, vn_rest) in
        register_eid info eid (vntyp vn)
      end
  in
  let do_vars ctx =
    dprintf "do_vars";
    (* For the first var, we need the eid! *)
    let hmm = match ctx.plusvars, ctx.minusvars with
      | [], [] ->
        None
      | [], v :: rest ->
        let vn = neg_var info v in
        Some (vn, do_vars_rest (vns_of_minusvars rest) ctx.constant)
      | v :: rest, minusvars ->
        let vns = (vns_of_plusvars ~plusvars:rest) @ (vns_of_minusvars ~minusvars) in
        Some (Hash v, do_vars_rest vns ctx.constant)
    in
    match hmm with
    | Some (Hash first_var, HInt (i, t)) when Big_int_convenience.bi_is_zero i ->
      (* This might legitimately happen after cancellations, constant folding etc *)
      begin
        try
          VH.find info.vn2eid first_var
        with Not_found ->
          (* XXX: not quite sure about this... *)
          Unique first_var
      end
    | Some (first_var, vn_rest) ->
      Bin (Type.PLUS, first_var, vn_rest)
    | None -> (* Just a constant *)
      begin
        match ctx.constant with
        | None ->
          Const (Int (Big_int_convenience.bi0, Type.Reg 32))
        | Some (i, t) ->
          Const (Int (i, t))
      end
  in
  dprintf "addsubctx2eid: %s" (addsub_ctx_to_str ctx);
  do_vars ctx

let norm_additions_subtractions info eid =
  (*
   * 1. Collect all leaves to add/sub/neg eids that are reachable from the
   *    root without going through an operator that is not add/sub/neg.
   *)
  match collect_leaves info eid with
  | None -> eid
  | Some ctx ->
    (* 2. Normalize the collected operands *)
    let ctx = simplify_addsubctx ctx in
    (* 3. Emit an expression tree in a canonical form *)
    addsubctx2eid info ctx

(* Perform some simplifications on an expid, using constant folding
   and some identities. *)
let opt_expid info var exp =
  let toconst (i,t) = Const(Int(i,t)) in
  let eid = get_expid info var exp in
  let sameas = function
    | Top -> eid
    | vn -> vn2eid info vn
  in
  match eid with
  (* constant folding *)
  | Bin(op, HInt v1, HInt v2) ->
    toconst (Arithmetic.binop op v1 v2)
  | Un(op, HInt v) ->
    toconst (Arithmetic.unop op v)
  | Cst(ct, t, HInt v) ->
    toconst (Arithmetic.cast ct v t)
  | It(HInt(bi,t), x, _) when bi_is_one bi ->
      sameas x
  | It(HInt(bi,t), _, y) when bi_is_zero bi ->
      sameas y
  | It(b, x, y) when x = y ->
      sameas x
  (* XXX: Extract(Shift) optimizations *)
  | Ex(h, l, HInt v) ->
    toconst (Arithmetic.extract h l v)
  | Con(HInt lv, HInt rv) ->
    toconst (Arithmetic.concat lv rv)
  (* phis can be constant*)
  | Ph(x::xs) as eid -> (
      match
        List.fold_left
          (function
            | Some x -> join x
            | None -> (fun _ -> None))
          (Some x) xs
      with
      | None -> eid
      | Some(HInt v) -> toconst v
      | Some(Hash _ as vn) -> vn2eid info vn
      | Some Top -> eid (* FIXME: what to do here? *)
    )
  (* identities on binops *)
  | Bin(AND, _, (HInt(bi,t) as v)) when bi_is_zero bi ->
      sameas v
  | Bin(AND, x, HInt(i,t)) when bi_is_minusone (Arithmetic.to_sbig_int (i,t)) ->
      sameas x
  | Bin(OR, x, HInt(bi,_)) when bi_is_zero bi ->
      sameas x
  | Bin(OR, _, (HInt(i,t) as v)) when bi_is_minusone (Arithmetic.to_sbig_int (i,t)) ->
      sameas v
  | Bin(XOR, x, HInt(bi,_))
  | Bin(PLUS, x, HInt(bi,_))
  | Bin(LSHIFT, x, HInt(bi,_))
  | Bin(RSHIFT, x, HInt(bi,_))
  | Bin(ARSHIFT, x, HInt(bi,_)) when bi_is_zero bi ->
      sameas x
  | Bin(TIMES, x, HInt(bi,_))
  | Bin(DIVIDE, x, HInt(bi,_))
  | Bin(SDIVIDE, x, HInt(bi,_)) when bi_is_one bi ->
      sameas x
  | Bin(AND, x, y)
  | Bin(OR, x, y)
      when x ==! y ->
      sameas x
  | Bin(EQ, x, y) when x ==! y ->
      Const(Ssa.val_true)
  | Bin(XOR, x, y) when x ==! y ->
      Const(Int(bi0, Var.typ var))
  | Bin(LT, _, HInt(bi,_)) when bi_is_zero bi ->
      Const(Ssa.val_false)
  | Bin(LE, _, HInt(i,t)) when bi_is_minusone (Arithmetic.to_sbig_int (i,t)) ->
      Const(Ssa.val_true)
        (* TODO: add SLT and SLE. Requires canonicalized ints *)
  | Bin(EQ, x, (HInt(bi,t))) when t = (Reg 1) && bi_is_zero bi ->
      sameas x
  | (Bin (PLUS, _, _) as eid)
  | (Bin (MINUS, _, _) as eid) ->
    norm_additions_subtractions info eid
  | Un (NOT, x) ->
    begin
      try
        begin
          match vn2eid info x with
          | Const (Int (i, t)) ->
            let i, t = Arithmetic.unop NOT (i, t) in
            Const (Int (i, t))
          | Un (NOT, y) ->
            sameas y
          | _ -> eid
        end
      with Not_found -> eid
    end
  | Cst (CAST_LOW, typ, x) ->
    begin
      try
        begin
          match vn2eid info x with
          | Const (Int (i, t)) ->
            let i, t = Arithmetic.cast CAST_LOW (i, t) typ in
            Const (Int (i, t))
          | Con (high, low) when vntyp low = typ ->
            sameas low
          | _ -> eid
        end
      with Not_found -> eid
    end
  (* | Bin(EQ, x, (HInt(0L,t))) when t = (Reg 1) -> *)
  (*     (Un(NOT, x)) *)
  | Ld (aryvn, idxvn, _, typ) ->
    (*
     * Do forwarding of stores to loads. I.e., if we see
     *     Store(aryX_2, aryX_1, store_idx, value, _, store_typ)
     * and there's a
     *     Load(aryX_2, load_idx, _, load_typ)
     * and the VNs of the indices match (as well as the types),
     * we can use the Stored value in place of the Load. Note
     * that we're only justified in removing memory accesses
     * when they are to things that can't fault (i.e. stack locals).
     *)
    begin
      try
        begin
          match vn2eid info aryvn with
          | St (staryvn, stidxvn, stvalvn, _, sttyp) when sttyp = typ ->
            dprintf "SCCVNLd: Found matching St (%s, %s)"
              (hash_to_string idxvn) (hash_to_string stidxvn);
            if vn_eq idxvn stidxvn then begin
              try
                vn2eid info stvalvn
              with Not_found -> eid
            end else begin
              dprintf "SCCVNLd: idxvn <> stidxvn";
              eid
            end
          | _ -> eid
        end
      with Not_found -> eid
    end
  | x -> x

(* simplifications in bap_opt which we don't (yet) do here:
   associative optimizations
   a - b = a + -b
   !(a-1) = -a
   redundant casts
*)


let lookup ~opt info var exp =
  dprintf "lookup %s" (Pp.var_to_string var);
  let get_eid = if opt then opt_expid else get_expid in
  try
    let eid = get_eid info var exp in
    dprintf "got eid %s for var %s and exp (%s)"
      (eid_to_str eid) (Pp.var_to_string var) (Pp.ssa_exp_to_string exp);
    try EH.find info.eid2vn eid
    with Not_found ->
      match eid with
      | Const(Var _) -> top
      | Const(Int(i,t)) -> HInt(i,t)
      | _ ->
          let h = Hash var in
          dprintf "adding eid (%s) -> vn (%s)" (eid_to_str eid) (hash_to_string h);
          EH.add info.eid2vn eid h;
          VH.add info.vn2eid var eid;
          h
  with Not_found -> (* no VNs for subexpressions yet *)
    top


module Dfs = Graph.Traverse.Dfs(G)

let fold_postfix_component f g v i=
  let acc = ref i in
  Dfs.postfix_component (fun x -> acc := f x !acc) g v;
  !acc


let rpo ~opt cfg =
  let info = {
    vn_h = VH.create 57;
    eid2vn = EH.create 57;
    vn2eid = VH.create 57;
    vn2prepends = VH.create 57;
  }
  in
  (* Contrary to the paper, only assigned SSA variables should have
     their hashes set to Top. Otherwise, uninitialized variables are
     all equivalent. *)
  let filter l = function
    | Move(v,e, _) ->
        VH.add info.vn_h v top;
        (v,e)::l
    | _ -> l
  in
  let moves=
    (* This has to be in postfix order for the algorithm to be correct! *)
    fold_postfix_component
      (fun b l ->
        List.fold_left filter l (List.rev(C.get_stmts cfg b))
      )
      cfg (C.G.V.create Cfg.BB_Entry) []
  in

  let () = (* add all other uninitialized vars as unique *)
    let vis = object
      inherit Ssa_visitor.nop
      method visit_rvar x =
        if not(VH.mem info.vn_h x) then (
          dprintf "Adding uninitialized variable %s" (Pp.var_to_string x);
          let h = Hash x
          and eid = Unique x in
          VH.add info.vn_h x h;
          VH.add info.vn2eid x eid;
          EH.add info.eid2vn eid h;
        );
        DoChildren
    end
    in
    C.G.iter_vertex
    (fun b -> ignore(Ssa_visitor.stmts_accept vis (C.get_stmts cfg b)))
    cfg;
  in
  let vn x =
    try VH.find info.vn_h x
    with Not_found -> failwith("vn: Unknown var: "^Pp.var_to_string x)
  in
  let lookup = lookup ~opt info in
  let count = ref 0 in
  let changed = ref true in
  let vhkeys vh = VH.fold (fun var _ acc -> var :: acc) vh [] in
  let vh2set vh = BatSet.of_list (vhkeys vh) in
  while !changed do
    changed := false;
    dprintf "Starting iteration %d" !count;
    incr count;
    List.iter
      (fun (v,e) ->
         let vars_before = vh2set info.vn_h in
         let oldvn = vn v in
         let temp = lookup v e in
         let vars_after = vh2set info.vn_h in
         (*
          * Determine which values have been added by our optimizer; record
          * them so that we can later emit definition statements too.
          * Note that since we use a Set, the vars are sorted by their ID
          * and they should also be defined in order of ID.
          *)
         let new_vars = BatSet.diff vars_after vars_before in
         BatSet.iter (fun var ->
             VH.add info.vn2prepends v var;
             dprintf "new_var: %s" (Pp.var_to_string var)) new_vars;
         if oldvn <>! temp (*&& temp <> top*) then (
           assert(temp <>! top); (* FIXME: prove this is always true *)
           changed := true;
           dprintf "Updating %s -> %s (was %s)" (Pp.var_to_string v) (hash_to_string temp) (hash_to_string oldvn);
           VH.replace info.vn_h v temp
         ) )
      moves;
  done;
  (******** END OF ALGORITHM FROM PAPER ******)
  let inverse = Hashtbl.create (VH.length info.vn_h) in
  let () = VH.iter (fun k v -> Hashtbl.add inverse v k) info.vn_h in
  let hash2equiv = Hashtbl.find_all inverse in
  if debug () then begin
      List.iter
        (fun (v,_) ->
           let h = vn v in
           let v2s = Pp.var_to_string in
           pdebug ("Var " ^ v2s v ^", Hash " ^ hash_to_string h ^ ", Equivs "^List.fold_left (fun s v -> s^v2s v^" ") "[" (hash2equiv h) ^"]"))
        moves
  end;
  (vn,hash2equiv,info.vn2eid, info.vn2prepends)


let hash_replacement hash2equiv vn2eid defsite psdom =
  let remove_dominated vars =
    let lt (_,d) (_,d') = psdom d d' in
    let rec extract_roots roots = function
      | [] ->
        roots
      | var :: rest ->
        begin
          (* If there exists a variable which dominates 'var', var
             cannot be a root *)
          if List.exists (fun x -> lt x var) rest then begin
            extract_roots roots rest
          end else if List.exists (fun x -> lt x var) roots then begin
            (* One of the previously found roots dominates our 'var',
               hence 'var' is not a root *)
            extract_roots roots rest
          end else begin
            (* No variable dominates 'var', ergo 'var' is a root *)
            extract_roots (var :: roots) rest
          end
        end
    in
    let var_defsites = List.rev_map (fun x -> (x, defsite x)) vars in
    List.map fst (extract_roots [] var_defsites)
  in
  (* cache the variables that are not dominated by an equivalent variable *)
  let myequiv_ht = Hashtbl.create 5700 in
  let hash2equiv x =
(*
   -- Is something wrong with the caching? -- agg
    try Hashtbl.find myequiv_ht x
    with Not_found ->
*)
      let res = remove_dominated (hash2equiv x) in
      Hashtbl.add myequiv_ht x res;
      res
  in
  fun pos hash ->
    let rec find_best p rest =
      match rest with
      | [] ->
        dprintf "find_best: []";
        None
      | v'::tl ->
        let p' = defsite v' in
        dprintf "find_best: %s (%s, %d)" (Pp.var_to_string v')
          (Cfg.SSA.v2s (fst p')) (snd p');
          if psdom p' p then
            Some v'
          else find_best p tl
    in
    match vn2eid hash with
    | Unique v when psdom (defsite v) pos ->
        Some(Var v)
    | Const c ->
        Some c
    | _ ->
      dprintf "hash_replacement: pos is (%s, %d)" (Cfg.SSA.v2s (fst pos)) (snd pos);
      match find_best pos (hash2equiv hash) with
      | Some v -> Some(Var v)
      | None -> None

let list_prepend f list =
  let rev = List.fold_left (fun acc el ->
      match f el with
      | None ->
        el :: acc
      | Some to_prepend -> (* Elements provided in proper order *)
        el :: ((List.rev to_prepend) @ acc)) [] list in
  List.rev rev

let stmt_prepender vn2eid vn2prepends stmts =
  let val_of_vn = function
    | Top -> failwith "val_of_vn: Top"
    | HInt (i, t) -> Ssa.Int (i, t)
    | Hash var -> Ssa.Var var
  in
  (*
   * Create a definition statement for this synthesized variable, based
   * on the eid.
   *)
  let def_of_var var =
    try
      begin
        match VH.find vn2eid var with
        | Bin (binop, vn1, vn2) ->
          Ssa.Move (var, Ssa.BinOp (binop, val_of_vn vn1, val_of_vn vn2),
                    [Type.Synthetic])
        | Un (unop, vn) ->
          Ssa.Move (var, Ssa.UnOp (unop, val_of_vn vn), [Type.Synthetic])
        | _ ->
          failwith "Unhandled eid in def_of_var"
      end
    with Not_found ->
      let s = Printf.sprintf "Couldn't find %s in vn2eid" (Pp.var_to_string var) in
      failwith s
  in
  let prepend stmt = match stmt with
    | Ssa.Move (avar, _, _) ->
      begin
        try
          begin
            (*
             * Do we need to prepend any definitions for values synthesized
             * by the optimizer?
             *)
            match VH.find_all vn2prepends avar with
            | [] ->
              None
            | vars ->
              let stmts = List.map def_of_var vars in
              (*
               * The vars are added to vn2prepends in order, find_all returns
               * them in reverse order, so here we need to flip them again.
               *)
              let stmts = List.rev stmts in
              List.iter (fun s ->
                  dprintf "Prepending %s to %s" (Pp.ssa_stmt_to_string s)
                    (Pp.ssa_stmt_to_string stmt)) stmts;
              Some stmts
          end
        with Not_found ->
          None
      end
    | _ ->
      None
  in
  list_prepend prepend stmts

let cfg_prepender vn2eid vn2prepends cfg =
  G.fold_vertex (fun v cfg ->
      let stmts = C.get_stmts cfg v in
      let stmts = stmt_prepender vn2eid vn2prepends stmts in
      C.set_stmts cfg v stmts) cfg cfg

(** Use SCCVN to elliminate redundant expressions, replacing them with a
    previously computed value. Some variables will no longer be used after
    this, so it may be beneficial to run dead code elimination after.

    @param opt Enable constant folding and algebraic simplifications.
    @return the new CFG and a bool indicating whether anything changed.
*)
let replacer ?(opt=true) cfg =
  let () = pdebug "Running rpo algorithm" in
  let (vn,hash2equiv,vn2eid_hash, vn2prepends) = rpo ~opt cfg in
  let () = pdebug "Compting dominators" in
  let psdom = pos_sdom cfg in
  let () = pdebug "Computing defsites" in
  let defsite = defsite cfg in
  let hash_replacement = hash_replacement hash2equiv (do_vn2eid (VH.find vn2eid_hash)) defsite psdom in
  let changed = ref false in
  let vis = object
    inherit Ssa_visitor.nop
    val mutable pos = (C.G.V.create Cfg.BB_Entry, 0)
    method set_pos p = pos <- p
    method visit_exp = function
      | Ssa.Phi (vars) ->
        dprintf "About to run hash_replacement for the vars of a Phi (%s)"
          (List.fold_left (fun acc v ->
               Printf.sprintf "%s, %s" acc (Pp.var_to_string v)) "" vars);
        begin
          let vars = List.map (fun v ->
              match hash_replacement pos (vn v) with
              | Some (Ssa.Var var) when v == var ->
                v
              | Some (Ssa.Var var) ->
                dprintf "Replacing phi var %s with %s" (Pp.var_to_string v)
                  (Pp.var_to_string var);
                changed := true;
                var
              | _ -> v) vars
          in
          ChangeTo (Ssa.Phi vars)
        end
      | _ ->
        DoChildren
    method visit_value = function
      | Ssa.Var v ->
        dprintf "About to run hash_replacement for the vn of %s" (Pp.var_to_string v);
          (match hash_replacement pos (vn v) with
           | Some(Ssa.Var var) when v == var -> SkipChildren
           | Some v' ->
               changed := true;
               dprintf "Replacing var %s with %s" (Pp.var_to_string v) (Pp.value_to_string v');
               ChangeTo v'
           | None -> SkipChildren
          )
      | _  -> SkipChildren

    method visit_stmt = function
      | Ssa.Move(_,Val _, _) -> (* visit value will handle that properly *)
          DoChildren
      | Ssa.Move(v,e, a) -> (
          match hash_replacement pos (vn v) with
          | Some vl ->
              changed := true;
              dprintf "Replacing exp %s with %s" (Pp.ssa_exp_to_string e) (Pp.value_to_string vl);
              ChangeTo(Move(v, Val vl, a))
          | None -> DoChildren
        )
      | _ -> DoChildren
  end
  in
  let somechange = ref false in
  let replace b cfg =
    let stmts =
      List.mapi
        (fun i s ->
           vis#set_pos (b,i);
           Ssa_visitor.stmt_accept vis s
        )
        (C.get_stmts cfg b)
    in
    if !changed then (
      somechange := true;
      changed := false;
      C.set_stmts cfg b stmts)
    else cfg
  in
  pdebug "Doing replacement";
  Cfg_pp.SsaStmtsDot.output_graph stderr cfg;
  let cfg = G.fold_vertex replace cfg cfg in
  Cfg_pp.SsaStmtsDot.output_graph stderr cfg;
  (*
   * The value calculations need to be added as a last step, since
   * previous code depends on statement offsets remaining stable.
   *)
  pdebug "Prepending value calculations";
  let cfg = cfg_prepender vn2eid_hash vn2prepends cfg in
  Cfg_pp.SsaStmtsDot.output_graph stderr cfg;
  (cfg, !somechange)


(** [aliased cfg] returns a function [f] to tell whether two values are
    aliased. [f x y] returns: Some true when [x=y], Some false when [x<>y],
    or None when it could not statically determine whether [x=y].
*)
let aliased cfg =
  let (vn, _, _, _) = rpo ~opt:false cfg in
  fun x y -> match (x,y) with
  | (Int(i,_), Int(i',_)) ->
      Some(i = i')
  | (Lab x, Lab y) when x = y ->
      Some true
  | (Var x, Var y) when vn x ==! vn y ->
      Some true
  | _ ->
      (* We could also check whether an lval was assigned a constant,
       * but running SCCVN.replace would get rid of any references to
       * such variables anyways. *)
      None


