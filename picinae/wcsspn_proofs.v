
Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import wcsspn_i386.

Import X86Notations.
(* binary natural number *)
Open Scope N.

(* The x86 lifter models non-writable code. *)
Theorem wcsspn_nwc: forall s2 s1, wcsspn_i386 s1 = wcsspn_i386 s2.
Proof. reflexivity. Qed.

(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem wcsspn_welltyped: welltyped_prog x86typctx wcsspn_i386.
Proof.
  Picinae_typecheck.
Qed.

(* Example #2: Memory safety
   wcsspn contains no memory-writes, and is therefore trivially memory-safe. *)
Theorem wcsspn_preserves_memory:
  forall_endstates wcsspn_i386 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign. admit. admit. admit. admit. Abort.
(* Qed. *)

(* Theorem wcsspn_preserves_ebx:
  forall_endstates wcsspn_i386 (fun _ s _ s' => s R_EBX = s' R_EBX).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed. *)

Theorem wcsspn_preserves_readable:
  forall_endstates wcsspn_i386 (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.


(* Define function exits *)
Definition wcsspn_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 65 | 86 => true
  | _ => false
  end | _ => false end.


(* Takes param string pointer p, character c and length n as parameter *)
(* defines character c is not contained upto index n of string p, excluding index n *)
Definition ncontains_upto (m: addr -> N) (p: addr) (c:N) (n:N) :=
  forall i, i< n -> m Ⓓ[p+i] <> c /\ m Ⓓ[p+i] <>0.

(* equivalent to ~contains we previously defined *)
Definition ncontains (m: addr -> N) (p: addr) (c:N) :=
exists n, ncontains_upto m p c n /\ (m Ⓓ[p + n] ) = 0.

(* first part: forall wcs1[i], i< return value, wcs[i] is contained in wcs2 *)
(* second part: wcs does not contain character at wcs[return value] *)
Definition postcondition_1 (m: addr -> N) (p1 p2: addr) (r:N): Prop :=
(forall i, i<r -> ~ncontains m p2 (m Ⓓ[p1 + i]) ) /\ ncontains m p2 (m Ⓓ[p1 + r] ).

(* edi: wcs1 , ebp:wcs2 *)
(* decide if passing value to invariant via parameter or extracting values from registers? *)
Definition wcsspn_invs (m:addr->N) (edi:N) (ebp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  (* exit_condition == postcondition_1 *)
  (* here all values are passed by parameter because registers are already popped by the retl instruction *)
  | 65 | 86=> Some(exists n, s R_EAX = Ⓓn /\postcondition_1 m edi ebp n)
  (* outer_loop_entry *)
  (* value in R_EAX is the index for outer loop *)
  (* i * 4 for indexing like the assembly code *)
  | 72 => Some(forall i, exists n, s R_EAX = Ⓓn /\ i < n -> ~ncontains m ebp (m Ⓓ[edi + 4*i]))
  (* inner_loop_entry *)
  | 52 => Some(forall i, exists outer_n inner_n char,
      (* R_EAX is the outer_loop index, EDX is inner loop index, EBX is the character currently pointed in wcs1 *)
      s R_EAX = Ⓓouter_n /\ s R_EDX = Ⓓinner_n /\ s R_EBX = Ⓓchar /\
      i < outer_n -> ~ncontains m ebp (m Ⓓ[edi + 4*i]) /\ 
      ncontains_upto m ebp char inner_n
    )
  |_ => None
  end | _ => None end.

Theorem wcsspn_partial_correctness:
  forall s edi ebp mem t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models x86typctx s)
         (EDI: s R_EDI = Ⓓ edi)(EBP: s R_EBP = Ⓓ ebp) (MEM: s V_MEM32 = Ⓜ mem),
  satisfies_all wcsspn_i386 ( wcsspn_invs mem edi ebp) wcsspn_exit ((x',s')::t).
  Proof.
    intros.
    assert (WTM0 := x86_wtm MDL MEM). simpl in WTM0.
    eapply prove_invs. simpl. rewrite ENTRY.

    (* Time how long it takes for each symbolic interpretation step to complete
      (for profiling and to give visual cues that something is happening...). *)
    Local Ltac step := time x86_step.

    (* Optional: The following proof ignores all flag values except CF and ZF, so
      we can make evaluation faster and shorter by telling Picinae to ignore the
      other flags (i.e., abstract their values away). *)
    Ltac x86_ignore v ::= constr:(match v with
      R_AF | R_DF | R_OF | R_PF | R_SF => true
    | _ => false end).

    (* Address 0 *)
    step. step. A.