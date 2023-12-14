
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
  prove_noassign.
Qed.

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
  forall i, i< n -> (m Ⓓ[p+4*i] <> c /\ m Ⓓ[p+4*i] <>0).

(* equivalent to ~contains we previously defined *)
Definition ncontains (m: addr -> N) (p: addr) (c:N) :=
exists n, (ncontains_upto m p c n /\ (m Ⓓ[p + 4*n] ) = 0).

(* first part: forall wcs1[i], i< return value, wcs[i] is contained in wcs2 *)
(* second part: wcs does not contain character at wcs[return value] *)
Definition postcondition_1 (m: addr -> N) (p1 p2: addr) (r:N): Prop :=
forall i, i<r -> ~ncontains m p2 (m Ⓓ[p1 + 4*i])  /\ (ncontains m p2 (m Ⓓ[p1 + 4*r]) \/ m Ⓓ[p1 + 4*r] = 0 ).


(* edi: wcs1 , ebp:wcs2 *)
(* decide if passing value to invariant via parameter or extracting values from registers? *)
Definition wcsspn_invs (m:addr->N) (esp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 6 => Some (s R_EAX = Ⓓ0 /\ s R_ESP = Ⓓesp)
  | 32 => Some(exists n, (s R_EAX = Ⓓn /\ forall i, i < n -> ~ncontains m (m Ⓓ[24+esp]) (m Ⓓ[m Ⓓ[20+esp] + 4*i]))
               /\ s R_EDI= Ⓓ (m Ⓓ[20+esp]) /\ s R_EBP= Ⓓ (m Ⓓ[24+esp] ) )
  (* here all values are passed by parameter because registers are already popped by the retl instruction *)
  | 65 | 86=> Some(exists n, (s R_EAX = Ⓓn /\ postcondition_1 m (m Ⓓ[20+esp]) (m Ⓓ[24+esp]) n))
  (* outer_loop_entry *)
  (* value in R_EAX is the index for outer loop *)
  (* i * 4 for indexing like the assembly code *)
  | 72 => Some(exists n, (s R_EAX = Ⓓn /\ forall i, i < n -> ~ncontains m (m Ⓓ[24+esp]) (m Ⓓ[m Ⓓ[20+esp] + 4*i]))
               /\ s R_EDI= Ⓓ (m Ⓓ[20+esp]) /\ s R_EBP= Ⓓ (m Ⓓ[24+esp] ) )
  (* inner_loop_entry *)
  | 52 => Some(
      (* R_EAX is the outer_loop index, EDX is inner loop index, EBX is the character currently pointed in wcs1 *)
      exists outer_n, (s R_EAX = Ⓓouter_n /\
      forall i, i < outer_n -> ~ncontains m (m Ⓓ[24+esp]) (m Ⓓ[m Ⓓ[20+esp] + 4*i]) ) /\
      exists inner_n char, (s R_EDX = Ⓓinner_n /\ s R_EBX = Ⓓchar /\ 
      ncontains_upto m (m Ⓓ[24+esp]) char inner_n )/\ 
      s R_EDI= Ⓓ (m Ⓓ[20+esp] ) /\ s R_EBP= Ⓓ ( m Ⓓ[24+esp]) 
    )
  |_ => None
  end | _ => None end.


Theorem wcsspn_partial_correctness:
  forall s esp mem t s' x'
         (ENTRY: startof t (x',s') = (Addr 6, s))
         (MDL: models x86typctx s)
         (EAX: s R_EAX = Ⓓ0) (ESP: s R_ESP = Ⓓesp) (MEM: s V_MEM32 = Ⓜ mem),
  satisfies_all wcsspn_i386 (wcsspn_invs mem esp) wcsspn_exit ((x',s')::t).
Proof.
    Local Ltac step := time x86_step.

    intros.
    eapply prove_invs. simpl. rewrite ENTRY. step. split; assumption.

    (* Optional: The following proof ignores all flag values except CF and ZF, so
      we can make evaluation faster and shorter by telling Picinae to ignore the
      other flags (i.e., abstract their values away). *)
    Ltac x86_ignore v ::= constr:(match v with
      R_AF | R_DF | R_OF | R_PF | R_SF => true
    | _ => false end).

    (* Address 0 *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    erewrite wcsspn_preserves_memory in MEM by eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply wcsspn_welltyped).
    assert (WTM := x86_wtm MDL MEM). simpl in WTM.
    clear - PRE MEM MDL WTM. rename t1 into t. rename s1 into s.

    destruct_inv 32 PRE.

    (* Address 6 *)
    destruct PRE as [EAX ESP].
    step. step. step. step. step.

      (* Jump 18 -> 61 *)
      step. step. step. step.
      exists 0. split. assumption. split.
        intros. contradict H. apply N.nlt_0_r.
          right. psimpl. apply N.eqb_eq in BC. symmetry. assumption.

    (* Jump 18 -> 20 *)
      step. step. step. exists 0. split. split. reflexivity. intros. contradict H.  apply N.nlt_0_r.
      split. reflexivity.
      reflexivity.
  (*See PRE, destruct PRE*)
    destruct PRE as [n H]. destruct H. destruct H. destruct H0. 
    (* Address 32 *)

      (* Jump 34 -> 61 *)
      step. step. apply N.eqb_eq in BC.
      step. step. step. step. exists n. 
      split.  assumption. 
        unfold postcondition_1. intros. 
      split. apply H1. assumption.
       left. unfold ncontains. exists 0. psimpl.
      split.

      (* Jump 34 -> 36 *)
      step. step. exists n. 
      split. 
        split. assumption.
        intros. apply H1. assumption.
      assumption.

        (* Jump 38 -> 72 *)
        admit.

        (* Jump 38 -> 40 *)
        step. step. admit.

    (* Address 52 *)
    step. step. step. step.

      (* Jump 59 -> 61 *)
      step. step. step. step. admit.

      (* Jump 59 -> 48 *)
      step. step.

        (* Jump 50 -> 72 *)
        admit.

        (* Jump 50 -> 52 *)
        admit.

    (* Address 72 *)
    step. step. step. step.

      (* Jump 80 -> 82 *)
      step. step. step. step. admit.

      (* Jump 80 -> 32 *)
      admit.
