
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


(* question regarding parameter types *)
(* check definition correctness *)
(* forall i, i < n /\ m [p +i] != 0 /\ m[p+n] = 0 *)
(* m Ⓓ[ a  ] *)
Definition haslength (m : addr -> N) (p: addr) (n: N) : Prop :=
   forall i, i< n /\ 0<m Ⓓ[ p + i ] /\ m Ⓓ[ p + n ]  = 0.

(* question regarding parameter types *)
(* forall n,exists i, haslength m p n ->  i < n -> m[p+i] = c *)
Definition contains (m: addr -> N) (p: addr) (c:N) : Prop :=
    forall n, exists i, haslength m p n -> i < n -> m Ⓓ[p+i] = c.

(* question regarding parameter types *)
(* p1 = s1 src, p2 = s2 dictionary, r returned prefix length s1 *)
Definition post_condition (m: addr -> N) (p1 p2: addr) (r:N): Prop :=
    forall n, haslength m p1 n -> r <= n /\ 
    forall i, i < r -> contains m p2 (m Ⓓ[p1 + i] ) /\
    ( (m Ⓓ[p1 + r] ) = 0 \/ ~contains m p2 (m Ⓓ[p1 + r] )).

(* Define function exits *)
Definition wcsspn_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 65 | 86 => true
  | _ => false
  end | _ => false end.

(* edi = wcs1, ebp = wcs2 *)
Definition exit_invariant (m:addr->N) (edi:N) (ebp:N) (esi:N) (ebx:N) (eax: N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  (* wcs1 is empty or wcs2 empty or wcs2 hit the end *)
  | 65 => Some(
        (* wcs1 is empty *)
        (ebx = 0 /\ s R_EAX = Ⓓ0) \/ 
        (* wcs2 is empty *)
        (esi= 0 /\ s R_EAX = Ⓓ0) \/ 
        (* ECX checks if at the end of wcs2 *)
        (s R_ECX = Ⓓ0 /\ 
          (post_condition m edi ebp 
              match (s R_EAX) with 
              | VaN n _ => n
              | _ => 0 end
          )
        )
      )
  (* wcs1 hit the end *)
  | 86 => Some(
      (ebx = 0 /\ 
        (post_condition m edi ebp 
            match (s R_EAX) with 
            | VaN n _ => n
            | _ => 0 end
        )
      )
  )
  | _ => None
  end | _ => None end.