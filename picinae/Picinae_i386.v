(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2023 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Instantiation of Picinae for Intel x86 ISA.         MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_finterp                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
   Then compile this module with menu option                   ZMMMMMMMM.$MM8$MN
   Compile->Compile_buffer.                                    $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from x86 native code: *)
Inductive x86var :=
  (* Main memory: MemT 32 *)
  | V_MEM32
  (* Flags (1-bit registers): *)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF (* NumT 1 *)
  (* Segment selectors (16-bit registers): *)
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS (* NumT 16 *)
  (* Floating point control register (16-bit): *)
  | R_FPU_CONTROL (* NumT 16 *)
  (* Floating point registers (80-bit): *)
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 (* NumT 80 *)
  (* General-purpose registers (32-bit): *)
  | R_EAX | R_EBX | R_ECX | R_EDX | R_EDI | R_ESI (* NumT 32 *)
  (* Stack pointer and base pointer (32-bit): *)
  | R_ESP | R_EBP (* NumT 32 *)
  (* Modifiable segment base registers (32-bit): *)
  | R_FS_BASE | R_GS_BASE (* NumT 32 *)
  (* Descriptor table registers (32-bit): *)
  | R_LDTR | R_GDTR (* NumT 32 *)
  (* SSE control register (32-bit): *)
  | R_MXCSR (* NumT 32 *)
  (* MMX and SSE registers (256-bit): *)
  | R_YMM0 | R_YMM1 | R_YMM2  | R_YMM3  | R_YMM4  | R_YMM5  | R_YMM6  | R_YMM7
  | R_YMM8 | R_YMM9 | R_YMM10 | R_YMM11 | R_YMM12 | R_YMM13 | R_YMM14 | R_YMM15
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  (* Temporaries introduced by the BIL lifter: *)
  | V_TEMP (n:N).

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniX86VarEq <: MiniDecidableType.
  Definition t := x86var.
  Definition eq_dec (v1 v2:x86var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniX86VarEq.

Module X86Arch <: Architecture.
  Module Var := Make_UDT MiniX86VarEq.
  Definition var := Var.t.
  Definition store := var -> value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = VaM r 32 /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = VaM w 32 /\ w a <> 0.
End X86Arch.

(* Instantiate the Picinae modules with the x86 identifiers above. *)
Module IL_i386 := PicinaeIL X86Arch.
Export IL_i386.
Module Theory_i386 := PicinaeTheory IL_i386.
Export Theory_i386.
Module Statics_i386 := PicinaeStatics IL_i386.
Export Statics_i386.
Module FInterp_i386 := PicinaeFInterp IL_i386 Statics_i386.
Export FInterp_i386.

Module PSimpl_i386 := Picinae_Simplifier_Base.
Export PSimpl_i386.
Module PSimpl_i386_v1_1 := Picinae_Simplifier_v1_1 IL_i386 Statics_i386 FInterp_i386.
Ltac PSimplifier ::= PSimpl_i386_v1_1.PSimplifier.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "i386_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "i386_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "i386_psimpl" "in" hyp(H) := psimpl_all_hyp H.
Tactic Notation "i386_psimpl" := psimpl_all_goal.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_i386_v1_0 := Picinae_Simplifier_v1_0 IL_i386 Statics_i386 FInterp_i386.
Ltac PSimplifier ::= PSimpl_i386_v1_0.PSimplifier.
*)

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition x86typctx v :=
  match v with
  | V_MEM32 => Some (MemT 32)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF => Some (NumT 1)
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS => Some (NumT 16)
  | R_FPU_CONTROL => Some (NumT 16)
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 => Some (NumT 80)
  | R_EAX | R_EBX | R_ECX | R_EDX | R_EDI | R_ESI => Some (NumT 32)
  | R_ESP | R_EBP => Some (NumT 32)
  | R_FS_BASE | R_GS_BASE => Some (NumT 32)
  | R_LDTR | R_GDTR => Some (NumT 32)
  | R_MXCSR => Some (NumT 32)
  | R_YMM0 | R_YMM1 | R_YMM2  | R_YMM3  | R_YMM4  | R_YMM5  | R_YMM6  | R_YMM7
  | R_YMM8 | R_YMM9 | R_YMM10 | R_YMM11 | R_YMM12 | R_YMM13 | R_YMM14 | R_YMM15 => Some (NumT 256)
  | A_READ | A_WRITE => Some (MemT 32)
  | V_TEMP _ => None
  end.

Definition x86_wtm {s v m w} := @models_wtm v x86typctx s m w.
Definition x86_regsize {s v n w} := @models_regsize v x86typctx s n w.



(* Create some automated machinery for simplifying symbolic expressions commonly
   arising from x86 instruction operations.  Mostly this involves simplifying
   (e mod 2^w) whenever e < 2^w. *)

(* Define an abbreviation for x86's parity flag computation, which produces
   uncomfortably large symbolic expressions. *)
Definition parity n :=
  N.lnot ((N.lxor
    (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
                      (N.lxor (N.shiftr n 4) n)) 1)
    (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
            (N.lxor (N.shiftr n 4) n))) mod 2^1) 1.

Lemma fold_parity: forall n,
  N.lnot ((N.lxor
    (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
                      (N.lxor (N.shiftr n 4) n)) 1)
    (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
            (N.lxor (N.shiftr n 4) n))) mod 2^1) 1
  = parity n.
Proof. intro. reflexivity. Qed.


(* Simplify memory access propositions by observing that on x86, the only part
   of the store that affects memory accessibility are the page-access bits
   (A_READ and A_WRITE). *)

Lemma memacc_read_frame:
  forall s v u (NE: v <> A_READ),
  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall s v u (NE: v <> A_WRITE),
  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall s v u1 u2,
  MemAcc mem_readable (update (update s v u2) A_READ u1) =
  MemAcc mem_readable (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall s v u1 u2,
  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.


(* getmem assembles bytes into words by logical-or'ing them together, but
   sometimes it is easier to reason about them as if they were summed.  The
   following theorem proves that logical-or and addition are the same when
   the operands share no common bits. *)
Theorem lor_plus:
  forall a b (A0: N.land a b = 0), N.lor a b = a + b.
Proof.
  intros. rewrite <- N.lxor_lor, N.add_nocarry_lxor by assumption. reflexivity.
Qed.

(* (a & b) ^ c = (a ^ c) & b whenever b & c = c *)
Lemma lxor_land:
  forall a b c, N.land b c = c -> N.lxor (N.land a b) c = N.land (N.lxor a c) b.
Proof.
 intros. apply N.bits_inj. apply N.bits_inj_iff in H. intro n. specialize (H n).
 do 2 rewrite N.land_spec, N.lxor_spec. rewrite <- H, N.land_spec.
 repeat destruct (N.testbit _ n); reflexivity.
Qed.

(* Simplify x86 memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H :=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* The user can ignore all assigned values to specified variables by
   redefining x86_ignore.  Example:
     Ltac x86_ignore v ::= constr:(match v with R_EAX => true | _ => false end).
 *)
Ltac x86_ignore v := constr:(false).
Ltac x86_abstract_vars H :=
  repeat match type of H with context [ update ?s ?v ?u ] =>
    let b := ltac:(x86_ignore v) in
    lazymatch eval cbv in b with true =>
      lazymatch u with
      | VaN ?n ?w =>
          tryif is_var n then fail else
          let tmp := fresh "n" in
          pose (tmp := n);
          change (update s v (VaN n w)) with (update s v (VaN tmp w)) in H;
          clearbody tmp
      | VaM ?m ?w =>
          tryif is_var m then fail else
          let tmp := fresh "m" in
          pose (tmp := m);
          change (update s v (VaM m w)) with (update s v (VaM tmp w)) in H;
          clearbody tmp
      end
    | _ => fail
    end
  end.

(* Values of IL temp variables are ignored by the x86 interpreter once the IL
   block that generated them completes.  We can therefore generalize them
   away at IL block boundaries to simplify the expression. *)
Ltac generalize_temps H :=
  repeat match type of H with context [ update ?s (V_TEMP ?n) ?u ] =>
    tryif is_var u then fail else
    lazymatch type of H with context [ Var (V_TEMP n) ] => fail | _ =>
      let tmp := fresh "tmp" in
      pose (tmp := u);
      change (update s (V_TEMP n) u) with (update s (V_TEMP n) tmp) in H;
      clearbody tmp;
      try fold value in tmp
    end
  end.

(* Symbolically evaluate an x86 machine instruction for one step, and simplify
   the resulting Coq expressions. *)
Ltac x86_step_and_simplify XS :=
  step_stmt XS;
  x86_abstract_vars XS;
  psimpl_vals_hyp XS;
  simpl_memaccs XS;
  destruct_memaccs XS;
  generalize_temps XS.

(* Introduce automated machinery for verifying an x86 machine code subroutine
   (or collection of subroutines) by (1) defining a set of Floyd-Hoare
   invariants (including pre- and post-conditions) and (2) proving that
   symbolically executing the program starting at any invariant point in a
   state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial
   correctness of the subroutine.

   In order for this methodology to prove that a post-condition holds at
   subroutine exit, we must attach one of these invariants (the post-condition)
   to the return address of the subroutine.  This is a somewhat delicate
   process, since unlike most other code addresses, the exact value of the
   return address is an unknown (defined by the caller).  We therefore adopt
   the convention that subroutines "exit" whenever control flows to an address
   for which no IL code is defined at that address.  This allows proving
   correctness of a subroutine by lifting only the subroutine to IL code (or
   using the pmono theorems from Picinae_theory to isolate only the subroutine
   from a larger program), leaving the non-subroutine code undefined (None). *)


(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).
   This slow-down can be avoided by sequestering prevalent injections into
   lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                      Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify (exitof a x) without expanding a. *)
Remark exitof_none a: exitof a None = Addr a. Proof eq_refl.
Remark exitof_some a x: exitof a (Some x) = x. Proof eq_refl.

(* If asked to step the computation when we're already at an invariant point,
   just make the proof goal be the invariant. *)
Ltac x86_invhere :=
  eapply nextinv_here; [ reflexivity | red; psimpl_vals_goal ].

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac x86_invseek :=
  apply NIStep; [reflexivity|];
  let sz := fresh "sz" in let q := fresh "q" in let s := fresh "s" in let x := fresh "x" in
  let IL := fresh "IL" in let XS := fresh "XS" in
  intros sz q s x IL XS;
  apply inj_prog_stmt in IL; destruct IL; subst sz q;
  x86_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             x86_step_and_simplify XS
         | exec_stmt _ (N.iter _ _ _) _ _ => fail
         | _ => x86_step_and_simplify XS
         end;
  try match goal with |- nextinv _ _ _ _ (_ :: ?xs :: ?t) =>
    let t' := fresh t in generalize (xs::t); intro t'; clear t; rename t' into t
  end;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac x86_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ x86_invseek; try x86_invhere | x86_invhere ].


Declare Scope i386_scope.
Delimit Scope i386_scope with i386.
Bind Scope i386_scope with stmt exp typ trace.
Open Scope i386_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : i386_scope.

Module X86Notations.

Notation "Ⓜ m" := (VaM m 32) (at level 20, format "'Ⓜ' m") : i386_scope. (* memory value *)
Notation "ⓑ u" := (VaN u 1) (at level 20, format "'ⓑ' u"). (* bit value *)
Notation "Ⓑ u" := (VaN u 8) (at level 20, format "'Ⓑ' u"). (* byte value *)
Notation "Ⓦ u" := (VaN u 16) (at level 20, format "'Ⓦ' u"). (* word value *)
Notation "Ⓓ u" := (VaN u 32) (at level 20, format "'Ⓓ' u"). (* dword value *)
Notation "Ⓠ u" := (VaN u 64) (at level 20, format "'Ⓠ' u"). (* quad word value *)
Notation "Ⓧ u" := (VaN u 128) (at level 20, format "'Ⓧ' u"). (* xmm value *)
Notation "Ⓨ u" := (VaN u 256) (at level 20, format "'Ⓨ' u"). (* ymm value *)
Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : i386_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : i386_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : i386_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 32 LittleE 8 m a) (at level 30) : i386_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 32 LittleE 16 m a) (at level 30) : i386_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 32 LittleE 32 m a) (at level 30) : i386_scope. (* read ymm from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : i386_scope. (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : i386_scope. (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : i386_scope. (* write dword to memory *)
Notation "m [Ⓠ a := v  ]" := (setmem 32 LittleE 8 m a v) (at level 50, left associativity) : i386_scope. (* write quad word to memory *)
Notation "m [Ⓧ a := v  ]" := (setmem 32 LittleE 16 m a v) (at level 50, left associativity) : i386_scope. (* write xmm to memory *)
Notation "m [Ⓨ a := v  ]" := (setmem 32 LittleE 32 m a v) (at level 50, left associativity) : i386_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End X86Notations.
