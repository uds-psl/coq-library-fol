Require Import FOL.ModelTheory.LogicalPrinciples.
Require Import FOL.ModelTheory.HenkinEnv.
Require Import FOL.ModelTheory.ReverseLS. 
Require Import FOL.ModelTheory.Core.

(** * Full Decomposition of DLS *)

Section LSiffDC.

    Corollary LS_iff_DC_under_CC_nat_LEM: 
        CC_nat -> LEM -> DLS <-> DC.
    Proof.
        intros H1 H2; split.
        - eapply LS_CC_impl_DC; eauto.
        - intros DC. eapply LS_downward_with_DC_LEM; eauto.
    Qed.

    Corollary LS_iff_DC_BDP_BEP_under_CC_nat:
        CC_nat -> DLS <-> DC /\ BDP /\ BEP.
    Proof.
        intros H1; split.
        - intros HLS. repeat split.
          now apply LS_CC_impl_DC.
          now apply LS_impl_BDP.
          now apply LS_impl_BEP.
        - intros (h1 & h2 & h3).
          now apply LS_downward_with_BDP_BEP_DC.
    Qed.

    Corollary LS_iff_DDC_BDP_BEP_BCC:
        DLS <-> DDC /\ BDP /\ BEP /\ BCC.
    Proof.
        split.
        - intros HLS. repeat split.
          assert (OBDC) as HO. now  apply LS_impl_OBDC.
          assert (BDC2) as H2. intros X x. now apply OBDC_impl_BDC2_on, HO.
          now apply BDC2_iff_DDC_BCC.
          now apply LS_impl_BDP. now apply LS_impl_BEP.
          now eapply BDC_impl_BCC, LS_impl_BDC. 
        - intros (h1 & h2 & h3 & h4).
          now apply  LS_downward.
    Qed.

    Theorem Decomposition1: 
      DLS -> DDC /\ BDP /\ BEP /\ BCC.
    Proof. now rewrite LS_iff_DDC_BDP_BEP_BCC. Qed.

    Theorem Decomposition2: 
      DDC /\ BDP /\ BEP /\ BCC -> BDP /\ BEP /\ BDC2.
    Proof.
      intros (h1 & h2 & h3 & h4). repeat split; eauto; now apply res_BDC2.
    Qed.

    Theorem Decomposition3:
      BDC2 /\ BDP /\ BEP -> OBDC.
    Proof.
      intros (h1 & h2 & h3).
      assert DDC as h4 by (now apply BDC2_impl_DDC).
      assert BCC. apply BDC_impl_BCC. now apply BDC2_impl_BDC.
      assert DLS by now rewrite LS_iff_DDC_BDP_BEP_BCC.
      now apply LS_impl_OBDC.
    Qed.

    Theorem Decomposition4:
      OBDC <-> DLS.
    Proof.
      split; [intro H; now apply LS_downward'|].
      apply LS_impl_OBDC.
    Qed.

End LSiffDC.
