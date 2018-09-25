(** Control flow graphs.  Control flow graphs contain nodes for each
    basic block of code, with edges between nodes representing a possible
    control flow.

    @author Ivan Jager
*)

(** {3 Basic block identifiers} *)

(** A basic block identifier. *)
type bbid =
    BB_Entry (** Entry node *)
  | BB_Exit   (** Return/exit node *)
  | BB_Indirect (** Indirect jump to/from a node *)
  | BB_Error (** Error node *)
  | BB of int (** Regular basic blocks *)

(** Convert a bbid to a string. *)
val bbid_to_string : bbid -> string

module BBid :
sig
  type t = bbid
  val compare : 'a -> 'a -> int
  val hash : bbid -> int
  val equal : 'a -> 'a -> bool
end

module BS : Set.S with type elt = BBid.t
module BH : Hashtbl.S with type key = BBid.t
module BM : Map.S with type key = BBid.t

(** {3 Control flow graphs} *)

(** The type of a control flow graph *)
module type CFG =
sig
  include Graph.Builder.S with type G.V.label = bbid and type G.E.label = bool option

  type lang

  (** Finds a vertex by a bbid *)
  val find_vertex : G.t -> G.V.label -> G.V.t

  (** Finds a vertex by a label in its stmts *)
  val find_label : G.t -> Type.label -> G.V.t

  (** Gets the statements from a basic block *)
  val get_stmts : G.t -> G.V.t -> lang

  (** Get an empty list of statements *)
  val default : lang

  (** Sets the statements for a basic block *)
  val set_stmts : G.t -> G.V.t -> lang -> G.t

  (** Joins two statement lists *)
  val join_stmts : lang -> lang -> lang

  (** Convert lang to string *)
  val lang_to_string : lang -> string

  (** Generate a new ID that wasn't previously generated for the given graph *)
  (* val newid : G.t -> bbid *)

  (** Creates a new vertex with new ID and adds it to the graph
      with the given statements. *)
  val create_vertex : G.t -> lang -> G.t * G.V.t

  (** Copy the metadata of a CFG without copying the vertices *)
  val copy_map : G.t -> G.t

  (* extra builder-like stuff *)
  val remove_vertex : G.t -> G.V.t -> G.t
  val remove_edge : G.t -> G.V.t -> G.V.t -> G.t
  val remove_edge_e : G.t -> G.E.t -> G.t

  (** Convert a vertex's label to a string *)
  val v2s : G.V.t -> string

end

module type S =
sig
    type lang

    module G : 
    sig 
        module V  : 
        sig 
            type t 
            type label 
        end
        module E :
        sig
            type t
        end
        type t
    end

    val find_vertex : G.t -> G.V.label -> G.V.t
    val get_stmts : G.t -> G.V.t -> lang
    val default : lang
    val join_stmts : lang -> lang -> lang
    val lang_to_string : lang -> string

    val fold_labels : (Type.label -> 'a -> 'a) -> lang -> 'a -> 'a
    val remove_labels : G.t -> G.V.t -> G.t

    val set_stmts : G.t -> G.V.t -> lang -> G.t
    val newid : G.t -> bbid * G.t

    val create_vertex : G.t -> lang -> G.t * G.V.t
    val remove_vertex : G.t -> G.V.t -> G.t

    val empty : unit -> G.t
    val copy : G.t -> G.t
    val add_vertex : G.t -> G.V.t -> G.t
    val add_edge : G.t -> G.V.t -> G.V.t -> G.t
    val add_edge_e : G.t -> G.E.t -> G.t
  
    val remove_edge : G.t -> G.V.t -> G.V.t -> G.t
    val remove_edge_e : G.t -> G.E.t -> G.t

    val copy_map : G.t -> G.t

    val v2s : G.V.t -> string 
end

module type Language =
sig
  type t
  val default : t
  val join : t -> t -> t
  val iter_labels : (Type.label->unit) -> t -> unit
  val to_string : t -> string
end

module Make (Lang: Language) : S with type lang = Lang.t

(** Control flow graph in which statements are in {!Ast.stmt} form. *)
module AST : CFG with type lang = Ast.stmt list

(** Control flow graph in which statements are in {!Ssa.stmt} form.
    All variables are assigned at most one time in the program, and
    expressions do not contain subexpressions. *)
module SSA : CFG with type lang = Ssa.stmt list

(** {3 Helper functions for CFG conversions} *)
(* These are for cfg_ast.ml and cfg_ssa.ml to be able to translate without
   breaking nextid. Poke Ivan if you think you need them for something else. *)

val map_ast2ssa : (Ast.stmt list -> Ssa.stmt list) -> AST.G.t -> SSA.G.t
val map_ssa2ast : (Ssa.stmt list -> Ast.stmt list) -> SSA.G.t -> AST.G.t
