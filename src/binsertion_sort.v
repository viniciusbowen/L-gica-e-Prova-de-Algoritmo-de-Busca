(* begin hide *)
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
(* end hide *)

(** A função [bsearch x l] retorna a posição [i] ($0 \leq i \leq |l|-1$) onde [x] deve ser inserido na lista ordenada [l]:
 *)

Function bsearch x l {measure length l} :=
  match l with
  | [] => 0
  | [y] => if (x <=? y)
           then 0
           else 1
  | h1::h2::tl =>
      let len := length l in
      let mid := len / 2 in
      let l1 := firstn mid l in
      let l2 := skipn mid l in
      match l2 with
      | [] => 0
      | h2'::l2' => if (x <? h2')
                    then bsearch x l1
                    else
                      if x =? h2'
                      then mid
                      else mid + (bsearch x l2)
      end
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt.
      * lia.
      * auto.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt.
      * lia.
      * auto.
  - intros. rewrite <- teq1. rewrite skipn_length. simpl length. apply Nat.sub_lt.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
      * lia.
      * auto.
    + apply Nat.div_str_pos. lia.
Defined.

(**
   Podemos fazer alguns testes com esta função:
 *)

Lemma test0: bsearch 1 [] = 0.
Proof.
  rewrite bsearch_equation. reflexivity.
Qed.

Lemma test1: bsearch 1 [0;2;3] = 1.
Proof.
  rewrite bsearch_equation. simpl. rewrite bsearch_equation. destruct (1 <=? 0) eqn: H.
  - inversion H.
  - reflexivity.
Qed.

Lemma test2: bsearch 2 [0;2;3] = 1.
Proof.
  rewrite bsearch_equation. simpl. reflexivity.
Qed.
  
Lemma test3: bsearch 2 [0;2;3;4] = 1.
Proof.
  rewrite bsearch_equation. simpl. rewrite bsearch_equation. simpl. reflexivity.
Qed.

Lemma test4: bsearch 3 [0;1;2;3;4;5] = 3.
Proof.
  rewrite bsearch_equation. simpl. reflexivity.
Qed.  


(**
  Daniel - Também podemos verificar que [bsearch x l] sempre retorna uma posição válida da lista [l]:
*)

Lemma bsearch_valid_pos: forall l x, 0 <= bsearch x l <= length l.
Proof.
  intros l x.
  functional induction (bsearch x l); try (simpl; lia).
  (* Tratamento automático para todos os casos de subdivisão que restarem *)
  all: try rewrite length_firstn in *.
  all: try rewrite skipn_length in *.
  all: assert (Hdiv: length (h1 :: h2 :: tl) / 2 < length (h1 :: h2 :: tl)) by (apply Nat.div_lt; simpl; lia).
  all: lia.
Qed.

(**
A seguir, definiremos a função [insert_at i x l] que insere o elemento [x] na posição [i] da lista [l]:
 *)

Fixpoint insert_at i (x:nat) l :=
  match i with
  | 0 => x::l
  | S k => match l with
           | nil => [x]
           | h::tl => h::(insert_at k x tl)
           end
  end.

Eval compute in (insert_at 2 3 [1;2;3]).

(**
  Daniel - Lemas auxiliares de sobre insert_at
*)

(**
  Daniel - 1. Prova que insert_at resulta em uma permutação da lista original adicionada de x
*)
Lemma insert_at_perm: forall l i x,
  Permutation (insert_at i x l) (x :: l).
Proof.
  induction l; intros i x.
  - destruct i; simpl; auto.
  - destruct i; simpl.
    + reflexivity.
    + eapply perm_trans.
      * apply perm_skip. apply IHl.
      * apply perm_swap.
Qed.

(**
  Daniel - 2. Tamanho da lista após inserção
*)

Lemma insert_at_length: forall l i x,
  length (insert_at i x l) = S (length l).
Proof.
  induction l; intros i x.
  - (* Caso base: lista vazia [] *)
    destruct i; simpl; reflexivity.
  - (* Caso indutivo: lista com elementos *)
    destruct i; simpl.
    + (* Subcaso i = 0 *)
      reflexivity.
    + (* Subcaso i = S i *)
      f_equal.
      apply IHl.
Qed.

(**
A função [binsert x l] a seguir insere o elemento x na posição retornada por [bsearch x l] de [l]:
*)

Definition binsert x l :=
  let pos := bsearch x l in
  insert_at pos x l.

(**
  Pessoa 2 - Lemas auxiliares sobre [Sorted] usados na prova de [binsert_correct].
*)

(**
  Pessoa 2 - Numa lista ordenada [a::l], o elemento [a] é [<=] TODOS os
  elementos de [l], não apenas o primeiro (que é tudo que [HdRel] garante
  diretamente). Isso é obtido propagando a transitividade de [<=] ao longo
  da recursão de [Sorted].
*)
Lemma Sorted_le_all : forall l a,
  Sorted le (a :: l) -> forall y, In y l -> a <= y.
Proof.
  induction l as [| b l' IH]; intros a Hsorted y Hy.
  - simpl in Hy. contradiction.
  - inversion Hsorted as [| a0 l0 Hs Hhd ]; subst.
    assert (Hab : a <= b) by (inversion Hhd; assumption).
    destruct Hy as [Heq | Hin].
    + subst y. exact Hab.
    + pose proof (IH b Hs y Hin) as Hby.
      apply Nat.le_trans with (m := b); assumption.
Qed.

(**
  Pessoa 2 - Um prefixo ([firstn]) de uma lista ordenada continua ordenado.
*)
Lemma Sorted_firstn : forall l n, Sorted le l -> Sorted le (firstn n l).
Proof.
  induction l as [| a l' IH]; intros n Hsorted.
  - destruct n; simpl; constructor.
  - destruct n as [| k].
    + simpl. constructor.
    + simpl. inversion Hsorted as [| a0 l0 Hs Hhd ]; subst.
      constructor.
      * apply IH. assumption.
      * destruct k as [| k'].
        -- simpl. constructor.
        -- destruct l' as [| b l''].
           ++ simpl. constructor.
           ++ simpl. constructor. inversion Hhd; assumption.
Qed.

(**
  Pessoa 2 - Um sufixo ([skipn]) de uma lista ordenada continua ordenado.
*)
Lemma Sorted_skipn : forall l n, Sorted le l -> Sorted le (skipn n l).
Proof.
  induction l as [| a l' IH]; intros n Hsorted.
  - destruct n; simpl; constructor.
  - destruct n as [| k].
    + simpl. assumption.
    + simpl. inversion Hsorted as [| a0 l0 Hs Hhd ]; subst.
      apply IH. assumption.
Qed.

(**
  Pessoa 2 - Lema central: se a posição [i] separa corretamente os
  elementos [<= x] (antes de [i]) dos elementos [>= x] (a partir de
  [i]), então inserir [x] na posição [i] preserva a ordenação. Este
  lema não menciona [bsearch]: é puramente sobre [insert_at].
*)
Lemma insert_at_sorted : forall i l x,
  i <= length l ->
  (forall y, In y (firstn i l) -> y <= x) ->
  (forall y, In y (skipn i l) -> x <= y) ->
  Sorted le l ->
  Sorted le (insert_at i x l).
Proof.
  induction i as [| k IH]; intros l x Hi Hbefore Hafter Hsort.
  - simpl. destruct l as [| h t].
    + constructor. constructor. constructor.
    + constructor.
      * exact Hsort.
      * constructor. apply Hafter. simpl. left. reflexivity.
  - destruct l as [| h t].
    + simpl in Hi. lia.
    + simpl in Hi. apply le_S_n in Hi.
      inversion Hsort as [| a0 l0 Hsort_t HdRel_h_t ]; subst.
      assert (Hbefore' : forall y, In y (firstn k t) -> y <= x).
      { intros y Hy. apply Hbefore. simpl. right. exact Hy. }
      assert (Hafter' : forall y, In y (skipn k t) -> x <= y).
      { intros y Hy. apply Hafter. simpl. exact Hy. }
      pose proof (IH t x Hi Hbefore' Hafter' Hsort_t) as IHt.
      simpl. constructor.
      * exact IHt.
      * destruct k as [| k'].
        -- simpl. constructor. apply Hbefore. simpl. left. reflexivity.
        -- destruct t as [| h' t'].
           ++ simpl in Hi. lia.
           ++ simpl. constructor.
              inversion HdRel_h_t as [| b l1 Hhh' ]; subst.
              exact Hhh'.
Qed.

(**
  Pessoa 2 - Lema que conecta [bsearch] com a hipótese exigida por
  [insert_at_sorted]: a posição retornada por [bsearch x l] realmente
  separa os elementos [<= x] dos elementos [>= x]. A prova segue por
  [functional induction] sobre [bsearch], espelhando os 7 ramos da
  definição da função (caso vazio, singleton em 2 subcasos, caso
  impossível l2 = [] e os 3 subcasos da subdivisão h1::h2::tl).
*)
(**
  Pessoa 2 - Dois fatos sobre [firstn]/[skipn] de uma lista concatenada
  [l1 ++ l2], quando o índice [i] cai inteiramente dentro de [l1].
  Usados para "traduzir" uma chamada recursiva de bsearch sobre a
  metade esquerda de volta para a lista inteira.
*)
Lemma firstn_app_le : forall (l1 l2 : list nat) i,
  i <= length l1 -> firstn i (l1 ++ l2) = firstn i l1.
Proof.
  induction l1 as [| a l1' IH]; intros l2 i Hi.
  - simpl in Hi. assert (Hi0 : i = 0) by lia. subst. reflexivity.
  - destruct i as [| k].
    + reflexivity.
    + simpl in Hi. simpl. f_equal. apply IH. lia.
Qed.

Lemma skipn_app_le : forall (l1 l2 : list nat) i,
  i <= length l1 -> skipn i (l1 ++ l2) = skipn i l1 ++ l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 i Hi.
  - simpl in Hi. assert (Hi0 : i = 0) by lia. subst. simpl. reflexivity.
  - destruct i as [| k].
    + reflexivity.
    + simpl in Hi. simpl. apply IH. lia.
Qed.

(**
  Pessoa 2 - Numa lista ordenada [P ++ a :: Q], todo elemento de [P]
  (a parte antes de [a]) é [<= a].
*)
Lemma Sorted_app_le : forall P a Q,
  Sorted le (P ++ a :: Q) -> forall y, In y P -> y <= a.
Proof.
  induction P as [| b P' IH]; intros a Q Hsorted y Hy.
  - simpl in Hy. contradiction.
  - simpl in Hy. destruct Hy as [Heq | Hin].
    + subst y. simpl in Hsorted.
      apply (Sorted_le_all (P' ++ a :: Q) b Hsorted).
      apply in_or_app. right. simpl. left. reflexivity.
    + simpl in Hsorted.
      inversion Hsorted as [| b0 l0 Hs Hhd ]; subst.
      apply (IH a Q Hs y Hin).
Qed.

(**
  Pessoa 2 - Análogos aos dois lemas acima, mas para quando o índice é
  exatamente [length l1 + k] (usado no caso em que a chamada recursiva
  de bsearch é sobre a metade direita, com deslocamento de mid).
*)
Lemma firstn_app_plus : forall (l1 l2 : list nat) k,
  firstn (length l1 + k) (l1 ++ l2) = l1 ++ firstn k l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 k; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma skipn_app_plus : forall (l1 l2 : list nat) k,
  skipn (length l1 + k) (l1 ++ l2) = skipn k l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 k; simpl.
  - reflexivity.
  - apply IH.
Qed.

(**
  Pessoa 2 - Versões "deslocadas" dos lemas anteriores: quando o índice
  é exatamente [length l1 + k], separamos a concatenação [l1 ++ l2]
  tomando [l1] inteiro e avançando [k] dentro de [l2].
*)
Lemma firstn_app_add : forall (l1 l2 : list nat) k,
  firstn (length l1 + k) (l1 ++ l2) = l1 ++ firstn k l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 k; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma skipn_app_add : forall (l1 l2 : list nat) k,
  skipn (length l1 + k) (l1 ++ l2) = skipn k l2.
Proof.
  induction l1 as [| a l1' IH]; intros l2 k; simpl.
  - reflexivity.
  - apply IH.
Qed.

(**
  Pessoa 2 - Fato básico: n / 2 <= n, provado via Nat.div_le_upper_bound
  em vez de depender de lia lidar diretamente com divisão (que se mostrou
  instável nesta versão do Rocq).
*)
Lemma div2_le : forall n, n / 2 <= n.
Proof.
  intro n. apply Nat.div_le_upper_bound; lia.
Qed.

(**
  Pessoa 2 - Fatos gerais sobre [firstn]/[skipn] quando o índice é uma
  soma [n + k]: dividir a lista em [n] primeiro, depois em [k] dentro
  do restante, dá o mesmo resultado que dividir direto em [n + k].
  Diferente de [firstn_app_add]/[skipn_app_add], estes lemas não exigem
  que a lista já esteja escrita como uma concatenação [l1 ++ l2], o que
  evita ter que "desmontar" [L] via [replace ... at N] (instável quando
  [L] e [M] foram introduzidos com [set]).
*)
Lemma firstn_skipn_add : forall (l : list nat) n k,
  firstn (n + k) l = firstn n l ++ firstn k (skipn n l).
Proof.
  induction l as [| a l' IH]; intros n k.
  - destruct n, k; reflexivity.
  - destruct n as [| n'].
    + reflexivity.
    + simpl. f_equal. apply IH.
Qed.

Lemma skipn_add : forall (l : list nat) n k,
  skipn (n + k) l = skipn k (skipn n l).
Proof.
  induction l as [| a l' IH]; intros n k.
  - destruct n, k; reflexivity.
  - destruct n as [| n'].
    + reflexivity.
    + simpl. apply IH.
Qed.

Lemma bsearch_split : forall l x,
  Sorted le l ->
  (forall y, In y (firstn (bsearch x l) l) -> y <= x) /\
  (forall y, In y (skipn (bsearch x l) l) -> x <= y).
Proof.
  intros l x Hsorted.
  functional induction (bsearch x l) using bsearch_ind.
  - (* l = [] *)
    split; intros y Hy; simpl in Hy; contradiction.
  - (* l = [y0], x <=? y0 = true, resultado = 0 *)
    split.
    + intros z Hz. simpl in Hz. contradiction.
    + intros z Hz. simpl in Hz. destruct Hz as [Heq | Hz]; [| contradiction].
      subst z. apply Nat.leb_le. assumption.
  - (* l = [y0], x <=? y0 = false, resultado = 1 *)
    split.
    + intros z Hz. simpl in Hz. destruct Hz as [Heq | Hz]; [| contradiction].
      subst z. apply Nat.leb_gt in e0. lia.
    + intros z Hz. simpl in Hz. contradiction.
  (* Caso l2 = [] : impossível, pois mid < length l quando
     length l >= 2 (usar Nat.div_lt + skipn_length para contradição). *)
  - exfalso.
    assert (Hmid_lt: length (h1 :: h2 :: tl) / 2 < length (h1 :: h2 :: tl)).
    { simpl length. apply Nat.div_lt; lia. }
    assert (Hskip_len: length (skipn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl))
                      = length (h1 :: h2 :: tl) - length (h1 :: h2 :: tl) / 2).
    { apply skipn_length. }
    rewrite e0 in Hskip_len.
    simpl length in Hmid_lt.
    simpl length in Hskip_len.
    lia.
  - (* Caso x <? h2' : chamada recursiva sobre l1 = firstn mid l *)
    apply Nat.ltb_lt in e1.
    assert (Hsorted_l1 : Sorted le (firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl))).
    { apply Sorted_firstn. exact Hsorted. }
    destruct (IHn Hsorted_l1) as [Hbefore1 Hafter1].
    assert (Hsplit : firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl)
                     ++ skipn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl)
                   = h1 :: h2 :: tl).
    { apply firstn_skipn. }
    rewrite e0 in Hsplit.
    assert (Hle : bsearch x (firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl))
                <= length (firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl))).
    { destruct (bsearch_valid_pos
                  (firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl)) x)
        as [_ Hle]. exact Hle. }
    assert (Hsorted_l2 : Sorted le (h2' :: l2')).
    { assert (Htmp : Sorted le (skipn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl))).
      { apply Sorted_skipn. exact Hsorted. }
      rewrite e0 in Htmp. exact Htmp. }
    split.
    + intros y Hy.
      rewrite <- Hsplit in Hy at 3.
      rewrite (firstn_app_le _ _ _ Hle) in Hy.
      apply Hbefore1. exact Hy.
    + intros y Hy.
      rewrite <- Hsplit in Hy at 3.
      rewrite (skipn_app_le _ _ _ Hle) in Hy.
      apply in_app_or in Hy.
      destruct Hy as [Hy1 | Hy2].
      * apply Hafter1. exact Hy1.
      * destruct Hy2 as [Heq | Hin].
        -- subst y. lia.
        -- assert (Hle2 : h2' <= y) by (apply (Sorted_le_all l2' h2' Hsorted_l2); exact Hin).
           lia.
  - (* Caso x =? h2' : resultado = mid *)
    apply Nat.eqb_eq in e2.
    assert (Hsorted_l2 : Sorted le (h2' :: l2')).
    { assert (Htmp : Sorted le (skipn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl))).
      { apply Sorted_skipn. exact Hsorted. }
      rewrite e0 in Htmp. exact Htmp. }
    assert (Hsplit : firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl)
                     ++ skipn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl)
                   = h1 :: h2 :: tl).
    { apply firstn_skipn. }
    rewrite e0 in Hsplit.
    split.
    + intros y Hy.
      rewrite e2.
      apply (Sorted_app_le (firstn (length (h1 :: h2 :: tl) / 2) (h1 :: h2 :: tl)) h2' l2').
      * rewrite Hsplit. exact Hsorted.
      * exact Hy.
    + intros y Hy.
      rewrite e0 in Hy.
      rewrite e2.
      destruct Hy as [Heq | Hin].
      * subst y. apply Nat.le_refl.
      * apply (Sorted_le_all l2' h2' Hsorted_l2). exact Hin.
  - (* Caso h2' < x (senão) : chamada recursiva mid + bsearch x l2 *)
    set (L := h1 :: h2 :: tl) in *.
    set (M := length L / 2) in *.
    apply Nat.ltb_ge in e1.
    apply Nat.eqb_neq in e2.
    assert (Hlt : h2' < x) by lia.
    assert (Hsorted_skipn : Sorted le (skipn M L)).
    { apply Sorted_skipn. exact Hsorted. }
    destruct (IHn Hsorted_skipn) as [Hbefore2 Hafter2].
    assert (Hsplit : firstn M L ++ skipn M L = L).
    { apply firstn_skipn. }
    assert (Hsorted_full_split : Sorted le (firstn M L ++ h2' :: l2')).
    { rewrite <- e0. rewrite Hsplit. exact Hsorted. }
    assert (HBig1 : firstn (M + bsearch x (skipn M L)) L
                  = firstn M L ++ firstn (bsearch x (skipn M L)) (skipn M L)).
    { apply firstn_skipn_add. }
    assert (HBig2 : skipn (M + bsearch x (skipn M L)) L
                  = skipn (bsearch x (skipn M L)) (skipn M L)).
    { apply skipn_add. }
    split.
    + intros y Hy.
      rewrite HBig1 in Hy.
      apply in_app_or in Hy.
      destruct Hy as [Hy1 | Hy2].
      * assert (Hy_le : y <= h2').
        { apply (Sorted_app_le (firstn M L) h2' l2' Hsorted_full_split y Hy1). }
        lia.
      * apply Hbefore2. exact Hy2.
    + intros y Hy.
      rewrite HBig2 in Hy.
      apply Hafter2. exact Hy.
Qed.

(** Agora podemos enunciar o teorema que caracteriza a correção da função [binsert], a saber, que [binsert x l] retorna uma lista ordenada, se [l] estiver ordenada: 
*)

Theorem binsert_correct: forall l x, Sorted le l -> Sorted le (binsert x l).
Proof.
  intros l x Hsorted.
  unfold binsert.
  destruct (bsearch_split l x Hsorted) as [Hbefore Hafter].
  apply insert_at_sorted; try assumption.
  destruct (bsearch_valid_pos l x) as [_ Hle].
  exact Hle.
Qed.

(**
   Alternativamente, podemos construir uma única função que combina a execução de [bsearch] e [insert_at]. A função [binsert x l] a seguir, recebe o elemento [x] e a lista ordenada [l] como argumentos e retorna uma permutação ordenada da lista [x::l]: 
 *)

Function binsert' x l {measure length l} :=
  match l with
  | [] => [x]
  | [y] => if (x <=? y)
           then [x; y]
           else [y; x]
  | h1::h2::tl =>
      let len := length l in
      let mid := len / 2 in
      let l1 := firstn mid l in
      let l2 := skipn mid l in
      match l2 with
      | [] => l
      | h2'::l2' => if x =? h2'
                    then l1 ++ (x ::l2)
                    else
                      if x <? h2'
                      then binsert' x l1
                      else binsert' x l2
      end
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt; lia.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt; lia.
  - intros. rewrite <- teq1. rewrite skipn_length. apply Nat.sub_lt.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt; lia.
    + simpl length. apply Nat.div_str_pos. lia.
Defined.

Lemma teste0: (binsert' 2 [1;2;3]) = [1;2;2;3].
Proof.
  rewrite binsert'_equation. simpl. reflexivity.
Qed.

(** As funções [binsert] e [binsert'] realizam o mesmo trabalho: *)

Lemma binsert_equiv_binsert': forall l x, binsert x l = binsert' x l.
Proof. 
  intros l x. functional induction (binsert' x l).
  simpl. try reflexivity.
  - admit.
Admitted.

(**
 E portanto a correção de [binsert'] é imediata:
*)

Corollary binsert'_correct: forall l x, Sorted le l -> Sorted le (binsert' x l).
Proof.
  intros l x H. rewrite <- binsert_equiv_binsert'. apply binsert_correct. assumption.
Qed.

(** O algoritmo principal é dado a seguir: *)

Fixpoint binsertion_sort (l: list nat) :=
  match l with
  | [] => []
  | h::tl => binsert h (binsertion_sort tl)
  end.

(** O teorema a seguir caracteriza a correção do algoritmo [binsertion_sort]. Observe que pode ser conveniente dividir esta prova em outras provas menores. Isto significa que a formalização pode ficar mais simples e mais organizada com a inclusão de novos lemas. *)

(**---------------------------------------
VINICIUS
 **)
(** 1. Lema de Permutação do binsert *)
Lemma binsert_perm: forall l x, Permutation (x :: l) (binsert x l).
Proof.
  intros l x.
  unfold binsert.
  (* Aplicamos a simetria para alinhar com o lema do Daniel *)
  apply Permutation_sym. 
  apply insert_at_perm.
Qed.

(** 2. A ordenação do algoritmo principal *)
Lemma binsertion_sort_Sorted: forall l, Sorted le (binsertion_sort l).
Proof.
  induction l as [| h tl IH].
  - (* Caso base: lista vazia *)
    simpl. constructor.
  - (* Caso indutivo: lista h :: tl *)
    simpl.
    (* O Thiago provou que binsert preserva a ordenação. 
       Pela Hipótese Indutiva (IH), (binsertion_sort tl) já está ordenado. *)
    apply binsert_correct.
    exact IH.
Qed.

(** 3. A permutação do algoritmo principal *)
Lemma binsertion_sort_Perm: forall l, Permutation l (binsertion_sort l).
Proof.
  induction l as [| h tl IH].
  - (* Caso base: lista vazia *)
    simpl. constructor.
  - (* Caso indutivo: lista h :: tl *)
    simpl.
    (* Precisamos provar que h::tl é permutação de binsert h (binsertion_sort tl).
       Faremos isso em dois saltos usando a transitividade. *)
    eapply perm_trans.
    + (* Salto 1: h::tl é permutação de h::(binsertion_sort tl) *)
      apply perm_skip. exact IH.
    + (* Salto 2: h::(binsertion_sort tl) é permutação de binsert h (binsertion_sort tl) *)
      apply binsert_perm.
Qed.



Theorem binsertion_sort_correct: forall l, Sorted le (binsertion_sort l) /\ Permutation l (binsertion_sort l).
Proof.
  intros l. induction l as [| h tl IH].
  - split.
    + simpl. apply Sorted_nil.
    + simpl. apply Permutation_refl.
  - destruct IH as [Hsorted Hperm].
    split.
    + apply binsert_correct. assumption.
    + apply binsertion_sort_Perm.
Qed.

(** Repositório: %\url{https://github.com/flaviodemoura/binsertion_sort}% *)