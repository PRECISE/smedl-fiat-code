Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Ascii.
Require Import
        Bedrock.Word
        Coq.Strings.Ascii
        Coq.Strings.String.

Section String.
  (* this has an exact idential structure to _FixList_ *)
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : MonoidUnit monoid bool}.

  Fixpoint format_string (xs : string) (ce : CacheFormat) : B * CacheFormat :=
    match xs with
    | EmptyString => (mempty, ce)
    | String x xs' => let (b1, env1) := format_ascii x ce in
                      let (b2, env2) := format_string xs' env1 in
                          (mappend b1 b2, env2)
    end.

  Fixpoint decode_string (s : nat) (b : B) (cd : CacheDecode) : string * B * CacheDecode :=
    match s with
    | O => (EmptyString, b, cd)
    | S s' => let (x1, e1) := decode_ascii b cd in
              let (x, b1) := x1 in
              let (x2, e2) := decode_string s' b1 e1 in
              let (xs, b2) := x2 in
              (String x xs, b2, e2)
    end.

  Local Opaque format_ascii.
  Theorem String_decode_correct :
    forall sz,
      format_decode_correct
        monoid
        (fun ls => length ls = sz)
        format_string (decode_string sz).
  Proof.
    unfold format_decode_correct.
    intros sz env env' xenv xenv' l l' bin' ext ext' Eeq Ppred Penc Pdec.
    generalize dependent sz. generalize dependent env. generalize dependent env'.
    generalize dependent xenv. generalize dependent xenv'. generalize dependent bin'.
    generalize dependent l'. generalize dependent ext'. induction l.
    { intros.
      inversion Penc; subst; clear Penc.
      rewrite mempty_left in Pdec. simpl in *.
      inversion Pdec. subst. intuition eauto. }
    { intros.
      destruct sz. inversion Ppred.
      simpl in *.
      destruct (format_ascii a env) eqn: ?.
      destruct (format_string l c) eqn: ?.
      inversion Penc; subst; clear Penc.
      inversion Ppred; subst; clear Ppred.
      rewrite <- mappend_assoc in Pdec.
      destruct (decode_ascii (mappend b (mappend b0 ext)) env') as [[? ?] ?] eqn: ?.
      destruct (Ascii_decode_correct _ _ _ _ _ _ _ _ _ Eeq I Heqp Heqp1) as [? [? ?]]. subst.
      destruct (decode_string (length l) (mappend b0 ext) c0) as [[? ?] ?] eqn: ?.
      specialize (IHl _ _ _ _ _ _ _ H Heqp0 _ eq_refl Heqp2).
      inversion Pdec; subst; clear Pdec.
      intuition eauto. subst. eauto. }
  Qed.
End String.
