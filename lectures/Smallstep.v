(** * Smallstep: Small-step Operational Semantics *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Lectures Require Import Maps.
From Lectures Require Import Imp.

Definition FILL_IN_HERE := <{True}>.

(* ================================================================= *)
(** ** Семантика большого шага

    Наша семантика для Imp выписана в т.н. стиле "big-step", или в стиле
    большого шага: правила вычисления вычисляют ответ для выражения
    (либо команды) "в один шаг":

      2 + 2 + 3 * 4 ==> 16

    Но с семантикой большого шага сложно говорить о том, что происходит
    _во время вычисления_...
*)

(* ================================================================= *)
(** ** Семантика малого шага

    Семантика _малого шага_: вместо моментального вычисления мы можем
    описывать, как "редуцировать" выражение к более простому виду, выполняя один
    шаг вычисления:

      2 + 2 + 3 * 4
      --> 2 + 2 + 12
      --> 4 + 12
      --> 16

    Преимущества семантики малого шага включают в себя:

        - Более точную "абстрактную машину", более близкую к настоящим
          реализациям;

        - Простой переход к многопоточным языкам и языкам с другого рода
          _вычислительными эффектами_;

        - Отделяет _расхождение_ (не-завершение) от _застревания_
          (ошибок исполнения).
*)

(* ################################################################# *)
(** * Игрушечный язык *)

(** Простейший язык программирования на свете: *)

Inductive tm : Type :=
  | C : nat -> tm         (* Константа *)
  | P : tm -> tm -> tm.   (* Сложение *)

(* ----------------------------------------------------------------- *)
(** *** Семантика большого шага в виде функции *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

(* ----------------------------------------------------------------- *)
(** *** Семантика большого шага в виде отношения

                               ---------                               (E_C)
                               C n ==> n

                               t1 ==> n1
                               t2 ==> n2
                           -------------------                         (E_P)
                           P t1 t2 ==> n1 + n2
*)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_C : forall n,
      C n ==> n
  | E_P : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

(* ----------------------------------------------------------------- *)
(** *** Отношение вычисления в семантике малого шага

                     -------------------------------                (ST_PCC)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_P1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_P2)
                      P (C n1) t2 --> P (C n1) t2'
*)
(** Обратите внимание:

       - каждый шаг вычисляет _самый левый_ подтерм [P], готовый к вычислению

             - первое правило говорит, как его вычислить

             - второе и третье -- как его найти

       - константы никуда не вычисляются
*)
(* ----------------------------------------------------------------- *)
(** *** Семантика малого шага в Rocq *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

(* ----------------------------------------------------------------- *)
(** *** Примеры *)

(** Если [t1] делает шаг в [t1'], то [P t1 t2] делает шаг в [P t1' t2]: *)

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_P1. apply ST_PCC.  Qed.

(* QUIZ

    Куда делает шаг следующий терм?

    P (P (C 1) (C 2)) (P (C 1) (C 2))

    (A) [C 6]

    (B) [P (C 3) (P (C 1) (C 2))]

    (C) [P (P (C 1) (C 2)) (C 3)]

    (D) [P (C 3) (C 3)]

    (E) Никуда из вышеперечисленного

_________________________________________________
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
*)
(* QUIZ

    Как насчёт этого?

    C 1

    (A) [C 1]

    (B) [P (C 0) (C 1)]

    (C) Никуда из вышеперечисленного

_________________________________________________
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
*)

End SimpleArith1.

(* ################################################################# *)
(** * Отношения *)

(** _Бинарное отношение_ на множестве [X] -- семейство утверждений,
    параметризованных двумя элементами [X] -- т.е., это утверждение о парах
    элементов [X].  *)

Definition relation (X : Type) := X -> X -> Prop.

(** Отношение шага [-->] -- пример отношения на [tm]. *)

(* ----------------------------------------------------------------- *)
(** *** Детерминизм *)

(** У отношения [-->], как и у семантики большого шага для Imp, есть одно
    простое свойство -- оно _детерминировано_ (aka _функционально_).

    _Теорема_: для любого [t] существует не более одного [t'] такого, что [t]
    делает шаг в [t'] (т.е., что [t --> t'] доказуемо). *)

(** В Rocq: *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PCC *) inversion Hy2; subst.
    + (* ST_PCC *) reflexivity.
    + (* ST_P1 *) inversion H2.
    + (* ST_P2 *) inversion H2.
  - (* ST_P1 *) inversion Hy2; subst.
    + (* ST_PCC *)
      inversion Hy1.
    + (* ST_P1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    + (* ST_P2 *)
      inversion Hy1.
  - (* ST_P2 *) inversion Hy2; subst.
    + (* ST_PCC *)
      inversion Hy1.
    + (* ST_P1 *) inversion H2.
    + (* ST_P2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.

(** Отступление про автоматизацию...

    Давайте определим небольшую тактику, чтобы сократить количество назойливых
    повторов в этом доказательстве: *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** Теперь наше доказательсто можно упростить... *)

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PCC *) reflexivity.
  - (* ST_P1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_P2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

(* ================================================================= *)
(** ** Значения *)

(** Про отношение [-->] полезно думать как про определение _абстрактной машины_:

      - _состоянием_ машины является терм.

      - _шаг_ машины -- атомарная единицы вычисления; в данном случае это одно
        применение операции сложения.

      - _состояния останова_ машины --
        те, из которых нельзя сделать ни одного шага.

    Тогда мы можем _исполнить_ терм [t] следующим образом:

      - Принимаем [t] начальным состоянием машины.

      - Используем отношение [-->], чтобы найти последовательность состояний,
        начинающихся с [t], такую, что из каждого состояния в последовательности
        можно перешагнуть в следующее.

      - Когда никакая редукция больше не возможна, "вычитать" итоговое состояние
        машины в качестве результата исполнения. *)

(** Заметим, что конечным состоянием нашей машины обязательно будут термы
    вида [C n] для некоторого [n].  Будем называть такие термы _значениями_. *)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

(** Кстати, правило шага [ST_P2] теперь можно переписать элегантнее:

                     -------------------------------                (ST_PCC)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_P1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_P2)
                         P v1 t2 --> P v1 t2'
*)

(** Имена переменных несут в себе важную информацию:
       - [v1] обязательно обозначает значение
       - [t1] и [t2] обозначают произвольные термы

    Так что гипотеза [value] в неформальном представлении, вообще говоря,
    избыточна: соглашение об именах уже сообщает нам, что её нужно будет
    добавить при переводе неформального правила в Rocq.  Здесь мы её оставим,
    но в дальнейшем в учебнике Programming Language Foundations она будет
    опущена. *)

(** Вот запись правила в Rocq: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(* ================================================================= *)
(** ** Продуктивность и нормальные формы *)

(** _Теорема_ (_Сильная продуктивность_): Если [t] -- терм, то либо [t]
    является значением, либо существует терм [t'] такой, что [t --> t']. *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C case *) left. apply v_C.
  - (* P case *) right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* t1 is a value *) destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* t2 is a value *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PCC.
      * (* t2 steps *)
        exists (P t1 t2').
        apply ST_P2; auto.
    + (* t1 steps *)
      exists (P t1' t2).
      apply ST_P1. apply Ht1.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Нормальные формы *)

(** Идею "продуктивности" (или "продвижения", или "прогресса") можно расширить,
    чтобы сформулировать ещё одно интересное свойство значений этого языка: они
    в точности совпадают с термами, _не_ продвигающимися в этом смысле.

    Чтобы сформулировать это наблюдение в Rocq, начнём с того, что назовём
    "термы, не могущие продвинуться", _нормальными формами_.  *)

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* ----------------------------------------------------------------- *)
(** *** Значения vs. нормальные формы *)

(* QUIZ

    Что такое _значение_ в этом языке?

    Что такое _нормальная форма_?
*)

(** В этом языке значения и нормальные формы совпадают: *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H contra.
  destruct contra. destruct H. inversion H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* следствие [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.

(** Почему это интересно?

    Потому что [value] -- синтаксическое понятие, т.е. оно определяется
    по записи терма; в свою очередь, [normal_form] -- понятие семантическое,
    ведь оно определяется исходя из отношения одношаговой семантики.

    То, что эти понятия должны высекать одно и то же подмножество термов,
    не очевидно!  *)

(** Действительно, мы легко могли бы (неправильно) выписать определения так,
    чтобы эти понятия _не_ совпадали... *)

(** Например, мы могли бы включить в [value]
    ещё не завершившие вычисление термы: *)

Module Temp1.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n)
  | v_funny : forall t1 n,
                value (P t1 (C n)).              (* <--- *)

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
(* QUIZ

    Используя неверное определение [value], к скольки различным "значениям"
    вычисляется следующий терм?

       P
         (P (C 1) (C 2))
         (C 3)

  ________________________________________
      Inductive value : tm -> Prop :=
        | v_C : forall n, value (C n)
        | v_funny : forall t1 n,
                      value (P t1 (C n)).

*)

(* QUIZ

    К скольки термам шагает (в смысле [step], определённого поверх неверного
    определения [value]) следующий терм (за один шаг)?

       P (P (C 1) (C 2)) (P (C 3) (C 4))

  ________________________________________
      Inductive value : tm -> Prop :=
        | v_C : forall n, value (C n)
        | v_funny : forall t1 n,
                      value (P t1 (C n)).
*)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
End Temp1.

(** Либо мы могли бы (вновь, неверно) определить [step] так, что он позволяет
    значениям продвигаться дальше. *)

Module Temp2.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).         (* Правильное определение value *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(* QUIZ

    В смысле этого определения, к скольки различным термам шагает следующий терм
    (за ровно один шаг)?

      P (C 1) (C 3)

   _______________________________________
     Inductive step : tm -> tm -> Prop :=
       | ST_Funny : forall n,
           C n --> P (C n) (C 0)
       | ST_PCC : forall n1 n2,
           P (C n1) (C n2) --> C (n1 + n2)
       | ST_P1 : forall t1 t1' t2,
           t1 --> t1' ->
           P t1 t2 --> P t1' t2
       | ST_P2 : forall v1 t2 t2',
           value v1 ->
           t2 --> t2' ->
           P v1 t2 --> P v1 t2'

*)
(* /QUIZ

    И вновь мы потеряем свойство, что значения совпадают с нормальными формами:
*)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

End Temp2.

(** Наконец, мы могли бы определить [value] и [step] так, что в языке
    есть некоторый терм, который _не_ является значением, и при этом также
    _не_ может сделать шаг.

    Такие термы называют _застрявшими_. *)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

(** (Обратите внимание, что [ST_P2] не хватает.) *)

(* QUIZ

    К скольким термам шагает следующий терм
    (в смысле определения выше, за один шаг)?

    P (C 1) (P (C 1) (C 2))

  _________________________________________
    Inductive step : tm -> tm -> Prop :=
      | ST_PCC : forall n1 n2,
          P (C n1) (C n2) --> C (n1 + n2)
      | ST_P1 : forall t1 t1' t2,
          t1 --> t1' ->
          P t1 t2 --> P t1' t2
*)

(** И вновь: *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

End Temp3.

(* ################################################################# *)
(** * Многошаговая редукция *)

(** Теперь мы можем использовать отношение одношаговой редукции и понятие
    значения, чтобы формализовать _исполнение_ абстрактной машины.

    Для начала мы определим _отношение многошаговой редукции_ [-->*], которое
    связывает терм [t] со _всеми_ термами, которых можно достичь некоторым
    конечным числом шагов из [t]. *)

(** Мы хотим переиспользовать идею многошаговой редукции много раз, с различными
    отношениями одношаговой редукции, так что давайте задержимся и введём общее
    понятие.

    Для произвольного отношения [R] (т.е. отношения шага [-->]) мы определяем
    новое отношение [multi R], называемое _многошаговым замыканием [R]_
    следующим образом. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** В результате такого определения [multi R] связывает два элемента [x] и [y],
    если

       - [x = y], или
       - [R x y], или
       - существует непустая последовательность [z1], [z2], ..., [zn] таких, что

           R x z1
           R z1 z2
           ...
           R zn y.

    Условно говоря, если [R] описывает один шаг вычисления, то [z1] ... [zn] --
    промежуточные шаги вычисления, которые приводят нас из [x] в [y]. *)

(** Отношение [multi step] на термах пишется как [-->*]. *)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** Отношение [multi R] обладает несколькими ключевыми свойствами.

    Во-первых, оно, очевидно, _рефлексивно_ (т.е., [forall x, multi R x x]).
    В случае отношения [-->*] (т.е. [multi step]) интуиция такова, что терм
    "вычисляется сам в себя за 0 шагов". *)

(** Во-вторых, оно включает [R], т.е. одношаговые редукции -- это частный случай
    редукций многошаговых.  (Этот факт и мотивирует слово "замыкание" в термине
    "многошаговое замыкание [R]".) *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

(** В-третьих, [multi R] _транзитивно_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.

(** В частности, для отношения [multi step] на термах, если [t1 -->* t2]
    и [t2 -->* t3], то [t1 -->* t3]. *)

(* QUIZ

    Какие из следующих отношений на числах _не могут_ быть выражены в виде
    [multi R] для некоторого [R]?

    (A) less than or equal

    (B) strictly less than

    (C) equal

    (D) none of the above
*)

(** Вот конкретная пара термов, связанных отношением [multi step]: *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_P1. apply ST_PCC. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_P2.
    - apply v_C.
    - apply ST_PCC. }
  apply multi_R.
  apply ST_PCC.
Qed.

(* ================================================================= *)
(** ** И вновь нормальные формы *)

(** Если [t] редуцируется к [t'] за 0 или более шагов и [t'] находится
    в нормальной форме, говорят, что "[t'] -- нормальная форма [t]". *)

Definition normal_form_of {X : Type} (R : relation X)  (t t' : X) :=
  ((multi R) t t' /\ normal_form R t').

(** Обратите внимание:

      - одношаговая редукция детерминирована;

      - так что, если [t] достигает нормальной формы, то эта нормальная форма
        единственная;

      - так что можно читать [normal_form t t'] как
        "[t'] -- нормальная форма [t]" (как если бы это была функция). *)

(** **** Упражнение: 3 звезды, стандартное, по желанию (normal_forms_unique) *)
Theorem normal_forms_unique:
  deterministic (normal_form_of step).
Proof.
  (* Рекомендуем оставить начало доказательства как есть! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** Однако для этого языка верно ещё более сильное утверждение:

       - редукция _любого_ терма [t] достигает нормальной формы за конечное
         число шагов.

    Другими словами, отношение [step] _нормализуется_ (или "для отношения
    [step] верна теорема о нормализации"). *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t', normal_form_of R t t'.

(** Чтобы доказать нормализацию [step],
    нам потребуется несколько лемм. *)

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_P1. apply H.
    + apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* Напомним, можно использовать [rewrite] и с "iff",
         не только с равенством: *)
      apply nf_same_as_value. apply v_C.

  - (* P *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    apply nf_same_as_value in Hnormal1.
    apply nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [n1].
    destruct Hnormal2 as [n2].
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2.
          - apply v_C.
          - apply Hsteps2. }
        apply multi_R. apply ST_PCC.
    + (* r *)
      apply nf_same_as_value. apply v_C.
Qed.

(* ================================================================= *)
(** ** Эквивалентность одношаговой и многошаговой семантик *)

(** Определив операционную семантику нашего крошечного языка программирования
    двумя способами (многошаговым и одношаговым), имеет смысл озадачиться,
    а одно и то же ли отношение задают эти два способа! *)

(** Докажем в обе стороны по отдельности. *)

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** Ключевые идеи доказательства можно увидеть на следующей иллюстрации:

       P t1 t2 -->            (по ST_P1)
       P t1' t2 -->           (по ST_P1)
       P t1'' t2 -->          (по ST_P1)
       ...
       P (C n1) t2 -->        (по ST_P2)
       P (C n1) t2' -->       (по ST_P2)
       P (C n1) t2'' -->      (по ST_P2)
       ...
       P (C n1) (C n2) -->    (по ST_PCC)
       C (n1 + n2)

    То есть, многошаговая редукция терма вида [P t1 t2] продвигается в три фазы:
       - Во-первых, мы используем [ST_P1] некоторое число раз, чтобы привести
         [t1] к нормальной форме, которая должна (по [nf_same_as_value]) быть
         термом вида [C n1] для некоторого [n1].
       - Далее, мы используем [ST_P2] некоторое число раз, чтобы привести [t2]
         к нормальной форме, которая вновь должна быть термом вида [C n2]
         для некоторого [n2].
       - Наконец, мы один раз используем [ST_PCC], чтобы редуцировать
         [P (C n1) (C n2)] в [C (n1 + n2)]. *)

Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** В обратном направлении нам будет достаточно одной леммы, устанавливающей
    взаимосвязь между одним шагом редукции и семантикой большого шага. *)

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Тот факт, что из многошаговой редукции следует семантика большого шага,
    теперь доказывается легко.

    Доказательство происходит индукцией по последовательности редукций,
    спрятанной в гипотезе [normal_form_of t t']. *)

Theorem multistep__eval : forall t t',
  normal_form_of step t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.


