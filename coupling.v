Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Require Export flows.
Set Default Proof Using "All".

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
Variable decisiveOp : (dOp → val).
Variable searchStrSpec : (dOp → val).
Variable lockLoc : node → loc.
Variable getLockLoc : val.
Variable alloc : val.

Definition lockNode : val :=
  rec: "lockN" "x" :=
    let: "l" := getLockLoc "x" in
    if: CAS "l" #false #true
    then #()
    else "lockN" "x" .

Definition unlockNode : val :=
  λ: "x",
  let: "l" := getLockLoc "x" in
  "l" <- #false.

Definition traverse : val :=
  rec: "tr" "p" "n" "k" :=
    match: (findNext "n" "k") with
      NONE => ("p", "n")
    | SOME "n'" =>
      lockNode "n'";; unlockNode "p";; "tr" "n" "n'" "k"
    end.

Definition searchStrOp (Ψ: dOp) (root: node) : val :=
  rec: "dictOp" "k" :=
    lockNode #root;;
    match: (findNext #root "k") with
      NONE => "dictOp" "k"  (* Need a way to modify root variable here! *)
    | SOME "n0" =>
      lockNode "n0";;
      let: "pn" := traverse #root "n0" "k" in
      let: "p" := Fst "pn" in
      let: "n" := Snd "pn" in
      let: "m" := alloc #() in
      let: "res" := (decisiveOp Ψ) "p" "n" "k" in
      unlockNode "p";; unlockNode "n";; "res"
    end.

(* ---------- Cameras used in the following proofs ---------- *)

(* RA for authoritative flow interfaces *)
Class flowintG Σ := FlowintG { flowint_inG :> inG Σ (authR flowintUR) }.
Definition flowintΣ : gFunctors := #[GFunctor (authR flowintUR)].

Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
Proof. solve_inG. Qed.

(* RA for authoritative set of nodes *)
Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR node)) }.
Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR node))].

Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
Proof. solve_inG. Qed.

(* RA for set of contents *)
Class contentG Σ := ContentG { content_inG :> inG Σ (authR (optionUR (exclR (gsetR key)))) }.
Definition contentΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (gsetR key))))].

Instance subG_contentΣ {Σ} : subG contentΣ Σ → contentG Σ.
Proof. solve_inG. Qed.

Section Coupling_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !contentG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* ---------- Flow interface set-up specific to this proof ---------- *)

  Variable root : node.

  Variable hrep : node → flowintUR → iProp.
  Parameter hrep_timeless_proof : ∀ n I, Timeless (hrep n I).
  Instance hrep_timeless n I : Timeless (hrep n I).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n, hrep n I_n -∗ ⌜Nds I_n = {[n]}⌝.

  Variable empty_node : node → iProp.
(*  Parameter hrep_timeless_proof : ∀ n, Timeless (empty_node n).
  Instance hrep_timeless n I : Timeless (empty_node n).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n, hrep n I_n -∗ ⌜Nds I_n = {[n]}⌝.
*)

  Hypothesis globalint_root_fp : ∀ I, globalint I → root ∈ Nds I.
  (* Hypothesis globalint_fpo : ∀ I, globalint I → FPo I = ∅. *)
  Hypothesis globalint_root_inr : ∀ I k, globalint I → k ∈ inreach I root.
  Hypothesis globalint_root_inset : ∀ I, globalint I → (∀ k, in_inset k I root).
  Hypothesis globalint_add : ∀ I I' I_m,
      globalint I → I' = I ⋅ I_m → is_empty_flowint I_m → globalint I'.
  Hypothesis contextualLeq_impl_globalint :
    ∀ I I', globalint I → contextualLeq I I' → globalint I'.

  (* The flow graphs store keyset of region in node abstraction *)
  Variable in_keyset : key → flowintUR → Prop.

  Hypothesis flowint_keyset : ∀ k I_n n,
      in_inset k I_n n ∧ not_in_outset k I_n n → in_keyset k I_n.
  Hypothesis flowint_keyset_mono : ∀ k I1 I2, in_keyset k I1 → in_keyset k (I1 ⋅ I2).

  (* ---------- Coarse-grained specification ---------- *)

  Definition Ψ dop k (C: gsetO key) (C': gsetO key) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (Is_true res ↔ k ∈ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (Is_true res ↔ k ∉ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (Is_true res ↔ k ∈ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.

  Lemma Ψ_determines_res dop k C1 C1' C2 C2' res1 res2 :
    Ψ dop k C1 C1' res1 ∗ Ψ dop k C2 C2' res2 ∗ ⌜C1 = C2⌝ -∗ ⌜res1 = res2⌝.
  Proof.
    destruct dop; iPureIntro; destr_bool;
      destruct H as ((HC1 & HkC1) & (HC2 & HkC2) & HEq);
      exfalso; rewrite HEq in HkC1; rewrite <- HkC2 in HkC1; inversion HkC1;
        contradiction.
  Qed.

  Lemma Ψ_determines_C' dop k C1 C1' C2 C2' res1 res2 :
    Ψ dop k C1 C1' res1 ∗ Ψ dop k C2 C2' res2 ∗ ⌜C1 = C2⌝ -∗ ⌜C1' = C2'⌝.
  Proof.
    destruct dop; iPureIntro; simpl; destr_bool;
      destruct H as ((HC1 & HkC1) & (HC2 & HkC2) & HEq); congruence.
  Qed.

  Axiom Ψ_keyset_theorem : ∀ dop k I_n I_n' I I' res,
      ⌜globalint I⌝ ∗ ⌜in_keyset k I_n⌝
      ∗ ⌜(∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o)⌝ ∗ ✓ I ∗ ✓ I'
      -∗ Ψ dop k (cont I_n) (cont I_n') res -∗ Ψ dop k (cont I) (cont I') res.


  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

  Parameter getLockLoc_spec : ∀ (n: node),
                  (<<< True >>> getLockLoc #n @ ⊤
                           <<< ∃ l:loc, ⌜lockLoc n = l⌝, RET #l >>>)%I.

  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
                  (<<< hrep n I_n >>> findNext #n #k @ ⊤
                              <<< ∃ (b: bool) (n': node), hrep n I_n ∗ (match b with true => ⌜in_edgeset k I_n n n'⌝ |
                                                                                     false => ⌜not_in_outset k I_n n⌝ end),
                                  RET (match b with true => (SOMEV #n') | 
                                                    false => NONEV end) >>>)%I.

  Parameter decisiveOp_3_spec : ∀ (dop: dOp) (I_p I_n I_m: flowintUR) (p n m: node) (k:key),
                  (<<< hrep p I_p ∗ hrep n I_n ∗ empty_node m ∗ ⌜is_empty_flowint I_m ⌝ ∗ ⌜Nds I_m = {[m]}⌝ 
                          ∗ ⌜✓I_m⌝ ∗ ⌜in_edgeset k I_p p n⌝ ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝ >>>
                             decisiveOp dop #p #n #k @ ⊤
                    <<< ∃ (b: bool) (I_p' I_n' I_m': flowintUR) (res: bool), 
                          match b with false => hrep p I_p' ∗ hrep n I_n' ∗ empty_node m 
                                                  ∗ Ψ dop k (cont (I_p ⋅ I_n)) (cont (I_p' ⋅ I_n')) res |
                                        true => hrep p I_p' ∗ hrep n I_n' ∗ hrep m I_m'
                                                ∗ Ψ dop k (cont (I_p ⋅ I_n ⋅ I_m)) (cont (I_p' ⋅ I_n' ⋅ I_m')) res
                                                ∗ ⌜Nds I_p' = {[p]}⌝ ∗ ⌜Nds I_n' = {[n]}⌝ ∗ ⌜Nds I_m' = {[m]}⌝
                                                ∗ ⌜contextualLeq (I_p ⋅ I_n ⋅ I_m) (I_p' ⋅ I_n' ⋅ I_m')⌝ end,
                          RET #res >>>)%I.



  (* ---------- The invariant ---------- *)

  Definition dictN : namespace := N .@ "dict".

  Definition main_inv (γ: gname) (γ_fp: gname) (γ_c: gname) I Ns C
    : iProp :=
    (own γ_c (● (Some (Excl C))) ∗ ⌜C = cont I⌝
        ∗ own γ (● I) ∗ ⌜globalint I⌝
        ∗ ([∗ set] n ∈ (Nds I), (∃ b: bool, (lockLoc n) ↦ #b
                                ∗ if b then True else (∃ (In: flowintUR),
                                                         own γ (◯ In) ∗ hrep n In ∗ ⌜Nds In = {[n]}⌝)))
        ∗ own γ_fp (● Ns) ∗ ⌜Ns = (Nds I)⌝
    )%I.

  Definition is_dict γ γ_fp γ_c :=
    inv dictN (∃ I Ns C, (main_inv γ γ_fp γ_c I Ns C))%I.

  Instance main_inv_timeless γ γ_fp γ_c I N C :
    Timeless (main_inv γ γ_fp γ_c I N C).
  Proof.
    rewrite /main_inv. repeat apply bi.sep_timeless; try apply _.
    try apply big_sepS_timeless. intros. apply bi.exist_timeless. intros.
    apply bi.sep_timeless; try apply _.
    destruct x0; try apply _.
  Qed.

  (* ---------- Assorted useful lemmas ---------- *)

  Lemma auth_set_incl γ_fp Ns Ns' :
    own γ_fp (◯ Ns) ∗ own γ_fp (● Ns') -∗ ⌜Ns ⊆ Ns'⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    rewrite auth_valid_discrete. simpl. rewrite ucmra_unit_right_id_L.
    intros. destruct H. inversion H0 as [m H1].
    destruct H1. destruct H2. apply gset_included in H2.
    apply to_agree_inj in H1. set_solver.
  Qed.

  Lemma auth_own_incl γ (x y: flowintUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H. destruct H. destruct H0 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y = y) as Hy.
    { rewrite /(⋅) /=. rewrite left_id. done. }
    rewrite Hy in Hb. rewrite <- Ha in Hb. done.
  Qed.

  Lemma auth_agree γ xs ys :
    own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
   iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  (** The view of the authority can be updated together with the local view. *)
  Lemma auth_update γ ys xs1 xs2 :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.


  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P I I_n I_n' x⌝ ∧ own γ x -∗
                       ∃ I', ⌜contextualLeq I I'⌝ ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝ 
                                ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (auth_auth_proj x); last first.
    - intros H. iIntros "(% & ?)". iExFalso. done.
    - intros p. intros H. case_eq p. intros q a Hp.
      iIntros "[% Hown]". destruct H0 as [I' H0].
      destruct H0. destruct H1. destruct H2. destruct H3.
      iExists I'.
      iSplit. iPureIntro. apply H3.
      iSplit. iPureIntro. apply H4.
      assert (Auth (auth_auth_proj x) (auth_frag_proj x) = x) as Hx.
      { destruct x. reflexivity. }
      assert (x = (Auth (Some (1%Qp, to_agree(I'))) (I_n'))) as H'. 
      { rewrite <-Hx. rewrite H. rewrite <-H2. rewrite Hp. rewrite H1.
       rewrite H0. reflexivity. }
      assert (● I' = Auth (Some (1%Qp, to_agree(I'))) ε) as HI'. { reflexivity. }
      assert (◯ I_n' = Auth ε I_n') as HIn'. { reflexivity. }
      assert (ε ⋅ I_n' = I_n') as HeIn.
      { rewrite /(⋅) /=. rewrite left_id. done. }
      assert (Some (1%Qp, to_agree I') ⋅ None = Some (1%Qp, to_agree I')) as Hs.
      { rewrite /(⋅) /=.
        rewrite /(cmra_op (optionR (prodR fracR (agreeR flowintUR))) (Some (1%Qp, to_agree I')) (None)) /=.
        reflexivity. }
      assert (● I' ⋅ ◯ I_n' = (Auth (Some (1%Qp, to_agree(I'))) (I_n'))) as Hd.
      { rewrite /(● I') /= /(◯ I_n') /=. rewrite /(⋅) /=.
        rewrite /(cmra_op (authR flowintUR) (Auth (Some (1%Qp, to_agree I')) ε) (Auth None I_n')) /=.
        rewrite /auth_op /=. rewrite HeIn. rewrite Hs. reflexivity. }
      iEval (rewrite Hd). iEval (rewrite <- H'). done.
  Qed.

  Parameter alloc_spec : ∀ γ γ_fp γ_c,
        is_dict γ γ_fp γ_c -∗ 
                <<< True >>> alloc #() @ ⊤∖↑dictN
                <<< ∃ (m: node) (I_m: flowintUR), own γ (◯ I_m) ∗ empty_node m ∗ ⌜Nds I_m = {[m]}⌝ 
                                                ∗ ⌜✓I_m⌝ ∗ ⌜is_empty_flowint I_m⌝, RET #m >>>.

  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)

  Lemma ghost_update_step γ γ_fp γ_c (n n': node) (k:key) (Ns: gset node) (I_n: flowintUR):
          is_dict γ γ_fp γ_c -∗ own γ (◯ I_n) ∗ ⌜Nds I_n = {[n]}⌝∗ ⌜in_inset k I_n n⌝ ∗ ⌜in_edgeset k I_n n n'⌝ 
                ={ ⊤ }=∗ ∃ (Ns': gset node), own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ ⌜n ∈ Ns'⌝ ∗ own γ (◯ I_n) ∗ ⌜root ∈ Ns'⌝.
  Proof.
    iIntros "#Hinv (HIn & % & % & %)".
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns' C) "(? & % & HI & % & ? & HNs' & %)".
    (* I = I_n ⋅ I2 *)
    iPoseProof (auth_own_incl with "[$HI $HIn]") as "%".
    unfold included in H5. destruct H5 as [I2 Hmult].
    (* n' ∈ FP I *)
    iPoseProof ((own_valid γ (● I)) with "HI") as "%".
    iAssert (⌜n' ∈ Nds I⌝)%I as "%".
    { iPureIntro.
      assert (n' ∈ Nds I2).
      { apply (flowint_step I I_n _ k n). done.
        by apply auth_auth_valid.
        replace (Nds I_n). set_solver. done. apply H3. }
      apply flowint_comp_fp in Hmult. set_solver.
    }
    (* snapshot fp to get Ns' *)
    iMod (own_update γ_fp (● Ns') (● Ns' ⋅ ◯ Ns') with "HNs'") as "HNs'".
    apply auth_update_core_id. apply gset_core_id. done.
    iEval (rewrite own_op) in "HNs'". iDestruct "HNs'" as "(HNs0 & HNs')".
    iAssert (⌜n ∈ Nds I⌝)%I as "%".
    { apply flowint_comp_fp in Hmult. rewrite H in Hmult. iPureIntro. set_solver. } 
    iAssert (⌜root ∈ Nds I⌝)%I as "%".
    { iPureIntro. apply globalint_root_fp. done. } 
    (* Close inv *)
    iMod ("HClose" with "[-HNs' HIn]").
    {
      iNext. iExists I, Ns', C. iFrame "# % ∗".
    }
    iModIntro. iExists Ns'. iFrame. iPureIntro. replace Ns'. set_solver. 
  Qed.

  Lemma ghost_update_step_2 γ γ_fp γ_c (n n': node) (k:key) (Ns: gset node) (I_n I_n': flowintUR):
          is_dict γ γ_fp γ_c -∗ own γ (◯ I_n) ∗ ⌜Nds I_n = {[n]}⌝ ∗ own γ (◯ I_n') ∗ ⌜Nds I_n' = {[n']}⌝
          ∗ ⌜in_inset k I_n n⌝ ∗ ⌜in_edgeset k I_n n n'⌝ ={ ⊤ }=∗ own γ (◯ I_n) ∗ own γ (◯ I_n') ∗ ⌜in_inset k I_n' n'⌝.
  Proof.
    iIntros "Hinv (HIn & % & HIn' & % & % & %)".
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns' C) "(? & % & HI & % & ? & HNs' & %)".
    (* I_n ≼ I ∧ I_n' ≼ I *)
    iPoseProof (auth_own_incl with "[$HI $HIn]") as "%".
    iPoseProof (auth_own_incl with "[$HI $HIn']") as "%".
    iAssert (⌜✓(I_n ⋅ I_n')⌝)%I with "[HIn HIn']" as "%".
    { iPoseProof (own_op γ (◯ I_n) (◯ I_n') with "[$HIn $HIn']") as "HIn".
      iEval (rewrite own_valid) in "HIn". iDestruct "HIn" as "%".
      iPureIntro. revert H8.
      apply auth_frag_proj_valid. }
    (* Close inv *)
    iMod ("HClose" with "[-HIn HIn']").
    {
      iNext. iExists I, Ns', C. iFrame "# % ∗".
    }
    iModIntro.
    iFrame. iPureIntro. by apply (flowint_inset_step I_n n I_n').
  Qed.

  Lemma ghost_update_root_inset γ γ_fp γ_c (k:key) (I_root: flowintUR):
          is_dict γ γ_fp γ_c -∗ own γ (◯ I_root) ∗ ⌜Nds I_root = {[root]}⌝ 
                                ={ ⊤ }=∗ own γ (◯ I_root) ∗ ⌜in_inset k I_root root⌝.
  Proof.
    iIntros "Hinv (HIn & %)".
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns' C) "(? & % & HI & % & ? & HNs' & %)".
    iPoseProof (auth_own_incl with "[$HI $HIn]") as "%".
    iPoseProof ((own_valid γ (● I)) with "HI") as "%".
    iAssert (⌜in_inset k I_root root⌝)%I as "%".
    { iPureIntro. apply (flowint_proj I); try done.
      by apply auth_auth_valid.
      by apply globalint_root_inset. }
    (* Close inv *)
    iMod ("HClose" with "[-HIn]").
    {
      iNext. iExists I, Ns', C. iFrame "# % ∗".
    }
    iModIntro. iFrame. iPureIntro. done.
  Qed.

  Lemma ghost_update_root_fp γ γ_fp γ_c :
          is_dict γ γ_fp γ_c -∗ True
                                ={ ⊤ }=∗ ∃ (Ns: gsetUR node), own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝.
  Proof.
    iIntros "Hinv Ht".
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns C) "(HC & % & HI & % & HIns & HNs & %)".
    (* snapshot fp to get Ns *)
    iMod (own_update γ_fp (● Ns) (● Ns ⋅ ◯ Ns) with "HNs") as "HNs".
    apply auth_update_core_id. apply gset_core_id. done.
    iEval (rewrite own_op) in "HNs". iDestruct "HNs" as "(HNs0 & HNs)".
    iMod ("HClose" with "[-HNs]").
    {
      iNext. iExists I, Ns, C. iFrame "# % ∗".
    }
    iModIntro. iExists Ns. iFrame.
    iPureIntro. replace Ns.
    by apply globalint_root_fp.
  Qed.

  (* ---------- Lock module proofs ---------- *)

  Lemma lockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node):
    is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗
          <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑dictN
          <<< ∃ (I_n: flowintUR), own γ (◯ I_n) ∗ hrep n I_n ∗ ⌜Nds I_n = {[n]}⌝, RET #() >>>.
  Proof.
    iIntros "#HInv [Hl1 Hl2]" (Φ) "AU". iLöb as "IH".
    wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "#Hl". iModIntro. wp_let. wp_bind (CmpXchg _ _ _)%E.
    iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7)". iDestruct "Hl" as %Hl.
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hl1 Hl2 H6 H7]" as "%".
    { (*iEval (rewrite <- H1).*) iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hl2" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I') n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']". iEval (rewrite Hl) in "Hlock". destruct b.
      - wp_cmpxchg_fail. iModIntro. iSplitR "Hl1 Hl2 AU". iNext. iExists I', N', C'. iFrame. iApply "hoho".
        iExists true. iEval (rewrite <-Hl) in "Hlock". iSplitL "Hlock". done. done. wp_pures.
        iDestruct "Hl1" as "#Hl1". iDestruct "Hl2" as "#Hl2". iApply "IH". done. done. done.
      - iMod "AU" as "[Ht [_ Hcl]]". iDestruct "Hlock'" as (In) "hehe".
        wp_cmpxchg_suc. iMod ("Hcl" with "hehe") as "HΦ".
        iModIntro. iModIntro. iSplitR "HΦ".
          * iNext. iExists I', N', C'. rewrite /main_inv. iFrame.
                iApply "hoho". iExists true. iEval (rewrite <-Hl) in "Hlock". iFrame.
          * wp_pures. done.
  Qed.

  Lemma unlockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node) :
    is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗
          <<< ∀ (I_n: flowintUR), hrep n I_n ∗ own γ (◯ I_n) ∗ ⌜Nds I_n = {[n]}⌝ >>>
                unlockNode #n    @ ⊤ ∖ ↑dictN
          <<< True, RET #() >>>.
  Proof.
    iIntros "#Hinv (Hfp & Hin)" (Φ) "AU". wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "Hl". iDestruct "Hl" as %Hl. iModIntro. wp_let. iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hfp Hin H6 H7]" as "%".
    { (*iEval (rewrite <- H1).*) iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hin" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I') n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']".
    iEval (rewrite Hl) in "Hlock".
    iMod "AU" as (I_n) "[Hr [_ Hcl]]". wp_store.
    iAssert (True)%I as "Ht". done.
    iMod ("Hcl" with "Ht") as "HΦ".
    iModIntro. iModIntro. iSplitR "HΦ". iNext. iExists I', N', C'. rewrite /main_inv. iFrame.
    iApply "hoho". iExists false. iEval (rewrite <-Hl) in "Hlock". iFrame. iExists I_n. 
    iDestruct "Hr" as "(? & ? & ?)". eauto with iFrame. done.
  Qed.

  (* ---------- Refinement proofs ---------- *)

  Lemma traverse_spec γ γ_fp γ_c (I_p I_n: flowintUR) (Ns: gset node) (p n: node) (k: key) :
    is_dict γ γ_fp γ_c -∗ hrep n I_n ∗ own γ (◯ I_n) ∗ ⌜Nds I_n = {[n]}⌝ ∗ ⌜in_inset k I_n n⌝
                          ∗ own γ_fp (◯ Ns) ∗ ⌜p ∈ Ns⌝ ∗ ⌜n ∈ Ns⌝ ∗ own γ (◯ I_p) 
                          ∗ hrep p I_p ∗ ⌜Nds I_p = {[p]}⌝ ∗ ⌜in_edgeset k I_p p n⌝ -∗
        <<< True >>>
                  traverse #p #n #k @ ⊤∖↑dictN
        <<< ∃ (p' n': node) (I_p' I_n': flowintUR), own γ (◯ I_p') ∗ own γ (◯ I_n') ∗ hrep p' I_p' ∗ hrep n' I_n'
                                          ∗ ⌜Nds I_p' = {[p']}⌝ ∗ ⌜Nds I_n' = {[n']}⌝ ∗ ⌜in_edgeset k I_p' p' n'⌝
                                          ∗ ⌜in_inset k I_n' n'⌝ ∗ ⌜not_in_outset k I_n' n'⌝,
              RET (#p', #n') >>>.
  Proof.
    iIntros "#Hinv H". iLöb as "IH" forall (p n Ns I_p I_n). iIntros (Φ) "AU".
    iDestruct "H" as "(Hrep & HIn & #HNdsN & #Hinset & #HNs & #HinP & #HinN & HIp & HrepP & #HNdsP & #Hedge)".
    wp_lam. wp_let. wp_let. wp_bind (findNext _ _)%E.
    awp_apply (findNext_spec n I_n k).
    iAaccIntro with "Hrep". eauto with iFrame.
    iIntros (b n') "(Hrep & Hb)". destruct b; last first.
    - iMod "AU" as "[Ht [_ HClose]]".
      iSpecialize ("HClose" $! p n I_p I_n).
      iMod ("HClose" with "[HIp HIn HrepP Hrep HNdsP HNdsN Hedge Hinset Hb]") as "HΦ".
      { eauto with iFrame. }
      iModIntro. wp_match. wp_pures. done.
    - iDestruct "Hb" as "#Hb".
      iDestruct (ghost_update_step γ γ_fp γ_c n n' k Ns I_n with "[Hinv] [HIn HNdsN Hinset Hb]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as (Ns')"(#HNs' & #Hin' & #Hin & HIn & #Hroot)".
      iModIntro. wp_pures. awp_apply (lockNode_spec γ γ_fp γ_c n' Ns'). done. eauto with iFrame.
      iAssert (True)%I as "Ht". { done. } iAaccIntro with "Ht". eauto with iFrame.
      iIntros (I_n') "(HIn' & Hrep' & #HNds')". iModIntro. wp_pures.
      awp_apply (unlockNode_spec γ γ_fp γ_c p Ns). done. eauto with iFrame.
      iAssert (hrep p I_p ∗ own γ (◯ I_p) ∗ ⌜Nds I_p = {[p]}⌝)%I with "[HrepP HIp HNdsP]" as "Haac". { eauto with iFrame. }
      iAaccIntro with "Haac". iIntros "(HrepP & HIp & _)". iModIntro. eauto with iFrame.
      iIntros. iModIntro. wp_pures. iSpecialize ("IH" $! n n' Ns' I_n I_n').
      iDestruct (ghost_update_step_2 γ γ_fp γ_c n n' k Ns I_n I_n' with "[Hinv] [HIn HNdsN HIn' HNds' Hinset Hb]") as ">HN".
      { done. } { eauto with iFrame. } iDestruct "HN" as "(HIn & HIn' & #Hb')".
      iApply ("IH" with "[Hrep' HIn' HNds' HIn Hrep]"). 
      { iFrame "Hrep' HIn' HNds' Hb' HNs' Hin Hin' HIn Hrep". eauto with iFrame. } done.
  Qed.

  Theorem searchStrOp_spec (γ γ_fp γ_c: gname) (dop: dOp) (k: key):
          ∀ (Ns: gsetUR node),
          is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜ root ∈ Ns ⌝ -∗
      <<< ∀ (C: gset key), own γ_c (◯ (Some (Excl C))) >>>
            (searchStrOp dop root) #k
                  @ ⊤∖↑dictN
      <<< ∃ (C': gset key) (res: bool), own γ_c (◯ (Some (Excl C'))) ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros (Ns). iIntros "#HInv H" (Φ) "AU". iLöb as "IH".
    iDestruct "H" as "#(Hfp & Hroot)". wp_lam. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec γ γ_fp γ_c root Ns). done. eauto with iFrame.
    iAssert (True)%I as "#Ht". { done. } iAaccIntro with "Ht". eauto with iFrame.
    iIntros (Ir) "(HIr & HrepR & #HNdsR)". iModIntro. wp_pures.
    wp_bind (findNext _ _)%E. awp_apply (findNext_spec root Ir k).
    iAaccIntro with "HrepR". eauto with iFrame.
    iIntros (b n) "(HrepR & Hb)". destruct b; last first.
    - iModIntro. wp_pures. iApply "IH". iFrame "Hfp Hroot". done.
    - iModIntro. wp_pures. wp_bind (lockNode _)%E. iDestruct "Hb" as "#Hb".
      iDestruct (ghost_update_root_inset γ γ_fp γ_c k Ir with "[HInv] [HIr HNdsR]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as "(HIr & #HinsetR)".
      iDestruct (ghost_update_step γ γ_fp γ_c root n k Ns Ir with "[HInv] [HIr HNdsR Hb HinsetR]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as (Ns') "(#Hfp' & #HinN & #HinR & HIr & _)".
      awp_apply (lockNode_spec γ γ_fp γ_c n Ns'). done. eauto with iFrame.
      iAaccIntro with "Ht". eauto with iFrame.
      iIntros (In) "(HIn & HrepN & #HNdsN)". iModIntro. wp_pures.
      wp_bind (traverse _ _ _)%E.
      iDestruct (ghost_update_step_2 γ γ_fp γ_c root n k Ns' Ir In with "[HInv] [HIr HNdsR HIn HNdsN HinsetR Hb]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as "(HIr & HIn & #HinsetN)".
      awp_apply (traverse_spec γ γ_fp γ_c Ir In Ns' root n k with "[] [HIr HIn HrepR HrepN]") . done.
      iFrame "HrepN HIn HNdsN HinsetN Hfp' HinR HinN HIr HrepR HNdsR Hb".
      iAaccIntro with "Ht". eauto with iFrame.
      iIntros (p' n' Ip' In') "(HIp' & HIn' & HrepP' & HrepN' & #HNdsP' & #HNdsN' & #HedgeP' & #HinsetN' & #HnotoutN')".
      iModIntro. wp_pures. wp_bind(alloc _)%E. awp_apply (alloc_spec γ γ_fp γ_c). done.
      iAaccIntro with "Ht". eauto with iFrame.
      iIntros (m Im) "(HIm & HempM & #HNdsM & #HM & #HempIntM)".
      iModIntro. wp_pures. wp_bind (decisiveOp _ _ _ _)%E. iDestruct "HempM" as "_".
      awp_apply (decisiveOp_3_spec dop Ip' In' Im p' n' m k).
      iAssert (empty_node m)%I as "HempM". { admit. }
      iAssert (hrep p' Ip' ∗ hrep n' In' ∗ empty_node m ∗ ⌜is_empty_flowint Im⌝ ∗ ⌜Nds Im = {[m]}⌝
               ∗ ⌜✓ Im⌝ ∗ ⌜in_edgeset k Ip' p' n'⌝ ∗ ⌜in_inset k In' n'⌝ ∗ ⌜not_in_outset k In' n'⌝)%I 
               with "[HrepP' HrepN' HempM]" as "Haac".
      { iFrame "HrepP' HrepN' HempM HempIntM HNdsM HM HedgeP' HinsetN' HnotoutN'". }
      iAaccIntro with "Haac". iIntros "(HrepP' & HrepN' & _)". iModIntro. iFrame "AU HIp' HIn' HrepP' HrepN' HIm".
      iIntros (b Ip'' In'' Im'' res) "Hb'". destruct b.
      + iDestruct "Hb'" as "(HrepP'' & HrepN'' & HrepM'' & #HΨ & #HNdsP'' & #HNdsN'' & #HNdsM'' & #Hcon)".
        iInv dictN as ">H". iDestruct "H" as (I N' C') "(HC & HCI & HI & Hglob & Hstar & HAfp & HINds)".
        iPoseProof (own_valid with "HI") as "%". 
        iAssert (own γ (◯ (Ip'⋅ In' ⋅ Im)))%I with "[HIp' HIn' HIm]" as "HIpnm'".
        { rewrite auth_frag_op. rewrite own_op. iFrame. rewrite auth_frag_op. rewrite own_op. iFrame. }
        iDestruct "Hcon" as %Hcon.
        iMod (own_updateP (flowint_update_P I (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im'')) γ
                          (● I ⋅ ◯ (Ip' ⋅ In' ⋅ Im)) with "[HI HIpnm']") as (Io) "H0".
        { apply (flowint_update I (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im'')). done. }
        { rewrite own_op. iFrame. }
        iPoseProof ((flowint_update_result γ I (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im''))
                      with "H0") as (I') "(% & % & HIIpnm)".
        iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
        iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
        iDestruct "HinsetN'" as %HinsetN'. iDestruct "HnotoutN'" as %HnotoutN'.
        iPoseProof ((Ψ_keyset_theorem dop k (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im'')
                                      I I' res) with "[-] [$HΨ]") as "#HΨI".
        { iFrame "# %". iFrame "Hglob". iPureIntro. repeat split.
          - apply flowint_keyset_mono. rewrite (comm op). apply flowint_keyset_mono.
            by apply (flowint_keyset k In' n').
          - apply auth_auth_valid. apply H.
          - apply auth_auth_valid. apply H2. }
        assert (Nds I = Nds I') as HFP. { apply contextualLeq_impl_fp. done. }
        iDestruct "HCI" as %HCI. iEval (rewrite <-HCI) in "HΨI". iDestruct "Hglob" as %Hglob.
        iMod "AU" as (C) "[hoho [_ Hcl]]".
        iDestruct (auth_agree with "HC hoho") as %Hauth.
        iMod (auth_update γ_c (cont I') with "HC hoho") as "[HC hoho]".
        iSpecialize ("Hcl" $! (cont I') res). iEval (rewrite <- Hauth) in "Hcl".
        iMod ("Hcl" with "[hoho HΨI]") as "HΦ". iFrame. iEval (rewrite <- Hauth). done.
        iDestruct "HIpnm''" as "((HIp'' & HIn'') & HIm'')". iModIntro. iSplitR "HrepP'' HrepN'' HIp'' HIn'' HΦ".
        * iNext. iExists I', N', (cont I'). unfold main_inv. iEval (rewrite HFP) in "Hstar".
          iEval (rewrite HFP) in "HINds". iFrame "HC HI' Hstar HAfp HINds". assert (globalint I') as HI'. 
          { by apply (contextualLeq_impl_globalint I I'). } iPureIntro. eauto.
        * iModIntro. wp_let. iDestruct "HΦ" as "_". awp_apply (unlockNode_spec γ γ_fp γ_c p' Ns').





