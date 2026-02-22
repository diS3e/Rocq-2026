(** * Poly: Полиморфизм и функции высшего порядка *)

(* Спрячем некоторые надоедливые предупреждения от Rocq: *)
Set Warnings "-notation-overridden".
From Lectures Require Export Lists.

(* ================================================================= *)
(** ** Полиморфные списки *)

(** Вместо того, чтобы объявлять по типу списков на тип элементов,
    например вот так... *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(** ...Rocq поддерживает _полиморфные_ определения, в том числе списков
    элементов произвольного типа: *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** Теперь можно использовать [list nat] вместо [natlist]. *)

(** Что такое сам [list]?

    Это _функция_ из типов в типы. *)

Check list : Type -> Type.

(** [X] из определения [list] также становится параметром конструкторов
    списка [nil] и [cons]. *)

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

(** Примечание: В файлах .v, квантор "forall" пишется явно, буквами.
    В соответствующих HTML-файлах он обычно отображается как стандартное
    математическое "перевёрнутое A". *)

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

(** Теперь мы можем определить полиморфные версии функций, которые мы
    видели ранее... *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* QUIZ

    Напомним типы [nil] и [cons]:

       nil : forall X : Type, list X
       cons : forall X : Type, X -> list X -> list X

    Каков тип [cons bool true (cons nat 3 (nil nat))]?

    (A) [nat -> list nat -> list nat]

    (B) [forall (X:Type), X -> list X -> list X]

    (C) [list nat]

    (D) [list bool]

    (E) Не типизируется
*)
(* QUIZ

    Напомним определение [repeat]:

    Fixpoint repeat (X : Type) (x : X) (count : nat)
                  : list X :=
      match count with
      | 0 => nil X
      | S count' => cons X x (repeat X x count')
      end.

    Каков тип [repeat]?

    (A) [nat -> nat -> list nat]

    (B) [X -> nat -> list X]

    (C) [forall (X Y: Type), X -> nat -> list Y]

    (D) [forall (X:Type), X -> nat -> list X]

    (E) Не типизируется
*)
(* QUIZ

    Каков тип [repeat nat 1 2]?

    (A) [list nat]

    (B) [forall (X:Type), X -> nat -> list X]

    (C) [list bool]

    (D) Не типизируется
*)

(* ----------------------------------------------------------------- *)
(** *** Вывод аннотаций типов *)

(** Вновь выпишем определение [repeat], но в этот раз не будем указывать типы
    аргументов.  Примет ли Rocq такое определение? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** Ну конечно.  Посмотрим, какой же тип он выдал [repeat']... *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** Rocq использовал _вывод типов_, чтобы выяснить правильные типы
    для [X], [x], and [count]. *)

(* ----------------------------------------------------------------- *)
(** *** Синтез аргументов-типов *)

(** Передавать каждый тип-_аргумент_ также избыточно, но Rocq обычно
    может их вывести: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Неявные аргументы *)

(** На самом деле, мы можем пойти ещё дальше и вообще не писать [_] в
    большинстве случаев, попросив Rocq _всегда_ выводить типовые аргументы
    некоторой функции.

    Директива [Arguments] сообщает имя функции (либо конструктора) и далее
    перечисляет имена аргументов (начиная с первых), которые нужно считать
    неявными; каждое такое имя окружено фигурными скобками. *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(** Теперь в данном примере нам вообще не нужно указывать типовые аргументы: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** Также мы можем объявить аргумент неявным ещё на этапе объявления функции,
    окружив его в фигурные скобки вместо круглых. Например: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** Вот полиморфные версии ещё пары функций, которые могут пригодиться
    нам позднее: *)

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Явная передача аргументов-типов *)

(** Как правило, позволять Rocq вывести все аргументы-типы нормально. Но
    всё же иногда это может привести к проблемам: *)

Fail Definition mynil := nil.

(** Мы можем исправить это явным объявлением типа: *)

Definition mynil : list nat := nil.

(** Также можно сделать все аргументы явными,
    добавив [@] перед именем функции. *)

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

(** Используя вывод аргументов и неявные аргументы, мы можем определить
    единую нотацию для списков произвольного типа. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(* QUIZ

    Какой тип Rocq присвоит следующему выражению?

       [1;2;3]

    (A) list nat

    (B) list bool

    (C) bool

    (D) Выражение не типизируется
*)
(* QUIZ

    Как насчёт этого?

       [3 + 4] ++ nil

    (A) list nat

    (B) list bool

    (C) bool

    (D) Выражение не типизируется
*)

(* QUIZ

    А это?

       andb true false ++ nil

    (A) list nat

    (B) list bool

    (C) bool

    (D) Не типизируется
*)

(* QUIZ

    Как насчёт этого?

        [1; nil]

    (A) list nat

    (B) list (list nat)

    (C) list bool

    (D) Не типизируется
*)

(* QUIZ

    Как насчёт этого?

        [[1]; nil]

    (A) list nat

    (B) list (list nat)

    (C) list bool

    (D) Не типизируется
*)

(* QUIZ

    А это?

         [1] :: [nil]

    (A) list nat

    (B) list (list nat)

    (C) list bool

    (D) Не типизируется
*)

(* QUIZ

    Это?

        @nil bool

    (A) list nat

    (B) list (list nat)

    (C) list bool

    (D) Не типизируется
*)

(* QUIZ

    Это?

        nil bool

    (A) list nat

    (B) list (list nat)

    (C) list bool

    (D) Не типизируется
*)

(* QUIZ

    Это?

        @nil 3

    (A) list nat

    (B) list (list nat)

    (C) list bool

    (D) Не типизируется
*)

(* ----------------------------------------------------------------- *)
(** *** Упражнения *)

(** **** Упражнение: 2 звезды, стандартное (poly_exercises)

    Ниже приведено несколько простых упражнений, в точности таких же, как в
    главе [Lists], чтобы попрактиковаться с полиморфизмом.
    Закончите доказательства ниже. *)

Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звезды, стандартное (more_poly_exercises)

    Вот несколько упражнений слегка поинтереснее... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Полиморфные пары *)

(** Аналогично... *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

(** Мы вновь можем воспользоваться механизмом [Нотаций], чтобы определить
    стандартную нотацию для _типов-произведений_ (т.е. типов пар): *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (Аннотация [: type_scope] сообщает Rocq, что это сокращение можно
    использовать только при синтаксическом разборе типов, но не при разборе
    выражений.  Это позволяет избежать коллизий с символом умножения.) *)

(** Не путайте [(x,y)] и [X*Y]! *)
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** Что делает эта функция? *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* ================================================================= *)
(** ** Полиморфные частичные значения *)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Функции как данные *)

(** Как и в большинстве современных языков программирования (особенно
    в "функциональных" ЯП, включая OCaml, Haskell, Racket, Scala, Clojure
    и т.д.), функции в Rocq являются _объектами первого класса_, что позволяет
    как передавать их в качестве аргументов другим функциям, так и возвращать в
    качестве результата, хранить их в структурах данных и т.д.. *)

(* ================================================================= *)
(** ** Функции высшего порядка *)

(** Функции, принимающие другие функции в качестве аргумента, называются
    функциями _высшего порядка_.  Вот простой пример: *)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Фильтрация списка *)

Fixpoint filter {X : Type} (test : X->bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(** Функция [filter] (особенно будучи скомбинированной с некоторыми
    другими функциями, которые мы увидим позже) позволяет программировать в
    _коллекционно-ориентированном_ стиле. *)

Definition countoddmembers' (l : list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Анонимные функции *)

(** Функции можно конструировать "на лету", не называя их. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(** Выражение [(fun n => n * n)] можно прочитать как "функция, которая, получив
    число [n], возвращает [n * n]." *)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Поэлементное отображение *)

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* QUIZ

    Напомним определение [map]:

      Fixpoint map {X Y : Type} (f : X->Y) (l : list X)
                   : list Y :=
        match l with
        | []     => []
        | h :: t => (f h) :: (map f t)
        end.

    Какой тип имеет @map?

    (A) forall X Y : Type, X -> Y -> list X -> list Y

    (B) X -> Y -> list X -> list Y

    (C) forall X Y : Type, (X -> Y) -> list X -> list Y

    (D) forall X : Type, (X -> X) -> list X -> list X
*)

(** Списки -- не единственный индуктивный тип, для которого можно осмысленно
    определить [map]. Вот определение [map] для типа [option]: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* ================================================================= *)
(** ** Свёртка *)

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Это "reduce" из map/reduce... *)

Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Example foldexample4 :
  fold (fun l n => length l + n) [[1];[];[2;3;2];[4]] 0 = 5.
Proof. reflexivity. Qed.

(* QUIZ

    Повторим ещё раз определение [fold]:

     Fixpoint fold {X Y : Type}
                   (f : X->Y->Y) (l : list X) (b : Y)
                 : Y :=
       match l with
       | nil => b
       | h :: t => f h (fold f t b)
       end.

    Какой тип имеет "@fold"?

    (A) forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y

    (B) X -> Y -> (X -> Y -> Y) -> list X -> Y -> Y

    (C) forall X Y : Type, X -> Y -> Y -> list X -> Y -> Y

    (D) X -> Y ->  X -> Y -> Y -> list X -> Y -> Y

*)

(* QUIZ

    До чего упрощается "fold plus [1;2;3;4] 0"?

   (A) [1;2;3;4]

   (B) 0

   (C) 10

   (D) [3;7;0]

*)

(* ================================================================= *)
(** ** Функции, конструирующие функции *)

(** Пример двух функций, _возвращающих_ функции в качестве результата. *)

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** Функция двух аргументов в Rocq -- на самом деле функция, возвращающая
    функцию! *)

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(** Похожим образом мы можем написать: *)
Definition fold_plus :=
  fold plus.

Check fold_plus : list nat -> nat -> nat.

