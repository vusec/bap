(** Type checking and inference for AST programs.

    @author Ed Schwartz
*)

exception TypeError of string
(** Exception raised when a type check error occurs. *)

(** {3 Type inference of expressions} *)

val infer_ast : ?check:bool -> Ast.exp -> Type.typ
(** [infer_ast e] returns the type of the expression [e].

    @param check If check is set, performs type checking on [e]. This
    parameter is deprecated.

    @raise TypeError if [check] is set and the expression does not
    type check.
*)

(** {3 Type checking} *)

val typecheck_expression : Ast.exp -> unit
(** [typecheck_expression e] type checks the expression [e].

    @raise TypeError if the expression does not type check.
*)

val typecheck_stmt : Ast.stmt -> unit
(** [typecheck_expression s] type checks the statement [s].

    @raise TypeError if the statement does not type check.
*)

val typecheck_prog : Ast.stmt list -> unit
(** [typecheck_expression p] type checks the program [p].

    @raise TypeError if the program does not type check.
*)

(** {3 Helper functions} *)

val is_integer_type : Type.typ -> bool
(** [is_integer_type t] returns true iff [t] is a register type. *)
val is_mem_type : Type.typ -> bool
(** [is_integer_type t] returns true iff [t] is of memory or array type. *)
val bits_of_width : Type.typ -> int
(** [bits_of_width t] returns the number of bits in the register type
    [t].

    @raise Invalid_argument if [t] is not of register type. *)
val bytes_of_width : Type.typ -> int
(** [bytes_of_width t] returns the number of bytes in the register
    type [t].

    @raise Invalid_argument if [t] is not of register type, or if t is
    a register type but its size is not expressible in bytes. *)
