(*****************************************************************************)
(*                 Tutorial: Listas, Parametrização e Trocq                  *)
(*                         — Passo a Passo —                                 *)
(*                                                                           *)
(*  Objetivo: entender como a parametrização de tipos nos permite reutilizar *)
(*  provas, e como o Trocq automatiza essa reutilização.                     *)
(*                                                                           *)
(*  Estrutura do arquivo:                                                    *)
(*    Parte 0  — Conceito central: o que é parametrização?                   *)
(*    Parte 1  — Lista de naturais (monomórfica): length, append, teorema    *)
(*    Parte 2  — Lista polimórfica: mesmas funções, mesmo teorema            *)
(*    Parte 3  — Comparando as provas (estilo tática)                        *)
(*    Parte 4  — ProofObjects: vendo as provas como termos lambda            *)
(*    Parte 5  — Conectando os dois mundos (preview do Trocq)                *)
(*                                                                           *)
(*****************************************************************************)


From Coq Require Import ssreflect.
From HoTT Require Import HoTT.

Set Universe Polymorphism.

(** Abre o escopo de nat para que literais como 0, 1, 2, 3 sejam
    interpretados como números naturais por padrão. *)
Local Open Scope nat_scope.

(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 0 — Conceito central: o que é parametrização?
  ══════════════════════════════════════════════════════════════════════

  Imagine que você precisa de listas de naturais, listas de booleanos,
  listas de strings, etc.  Sem parametrização, você teria que definir
  um tipo separado para cada um e reescrever TODAS as funções (length,
  append, reverse...) e TODAS as provas uma segunda vez.

  Com parametrização (ou polimorfismo paramétrico), você define as
  operações UMA VEZ para um tipo A genérico, e toda instância (nat,
  bool, string...) herda automaticamente as propriedades provadas.

  A ideia fundamental:

      "Propriedades que dependem apenas da ESTRUTURA da lista (e não do
       TIPO dos seus elementos) são automaticamente válidas para qualquer
       instância."

  Este tutorial demonstra isso de forma concreta, começando do zero.
*)


(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 1 — Lista de naturais (monomórfica)

  Definimos um tipo de lista específico para nat, como se ainda não
  conhecêssemos o polimorfismo.  Isso é exatamente o "ponto de partida"
  sem generalização: um tipo, uma implementação, uma prova.
  ══════════════════════════════════════════════════════════════════════
*)

(** O tipo: uma lista de naturais é ou vazia (NNil) ou um nat seguido
    de outra lista (NCons h t). *)
Inductive NatList : Type :=
  | NNil  : NatList
  | NCons : nat -> NatList -> NatList.

(** Notações para escrever listas de forma legível. *)
Notation "x :n: l" := (NCons x l) (at level 60, right associativity).
Notation "[[]]"    := NNil.

(** Comprimento da lista: conta o número de elementos. *)
Fixpoint nlength (l : NatList) : nat :=
  match l with
  | NNil       => O
  | NCons _ t  => S (nlength t)
  end.

(** Concatenação: põe os elementos de l1 antes dos de l2. *)
Fixpoint napp (l1 l2 : NatList) : NatList :=
  match l1 with
  | NNil       => l2
  | NCons h t  => NCons h (napp t l2)
  end.

(** Verificações rápidas *)
Example nlength_ex1 : nlength [[]] = O.
Proof. simpl. reflexivity. Qed.

Example nlength_ex2 : nlength (S O :n: S (S O) :n: S (S (S O)) :n: [[]]) = S (S (S O)).
Proof. simpl. reflexivity. Qed.

Example nlength_ex3 : nlength (1 :n: 2 :n: 3 :n: [[]]) = 3.
Proof. simpl. reflexivity. Qed.

Example napp_ex :
  napp (1 :n: 2 :n: [[]])
       (3 :n: 4 :n: [[]]) = (1 :n: 2 :n: 3 :n: 4 :n: [[]]).
Proof. simpl. reflexivity. Qed.

(** ── Teorema principal (Parte 1) ────────────────────────────────────

    "O comprimento da concatenação é a soma dos comprimentos."

    Este é o teorema que vamos provar de 3 formas diferentes ao longo
    deste arquivo: por tática, como ProofObject e via Trocq.
*)
Theorem nlength_napp :
  forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
Proof.
  intros l1 l2.
  (** Indução na estrutura de l1 — a variável l2 fica fixa. *)
  induction l1 as [| h t IH].
  - (** Caso base: l1 = NNil
        Ambos os lados reduzem a  [nlength l2]  por computação.
        [simpl] expande as definições de napp e nlength:
          nlength (napp NNil l2)  = nlength l2
          nlength NNil + nlength l2 = 0 + nlength l2 = nlength l2  *)
    simpl. reflexivity.
  - (** Passo indutivo: l1 = NCons h t
        Hipótese indutiva (IH): nlength (napp t l2) = nlength t + nlength l2
        Meta após [simpl]:
          S (nlength (napp t l2)) = S (nlength t + nlength l2)    *)
    simpl.
    (** [rewrite IH] substitui o lado esquerdo de IH no goal, deixando:
          S (nlength t + nlength l2) = S (nlength t + nlength l2)  *)
    rewrite IH.
    reflexivity.
Qed.


(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 2 — Lista polimórfica (paramétrica)

  Agora generalizamos: em vez de fixar o tipo dos elementos como nat,
  tornamos o tipo um PARÂMETRO  A : Type.

  Observe que a definição e as funções são estruturalmente idênticas
  às da Parte 1.  A única diferença é o parâmetro A.
  ══════════════════════════════════════════════════════════════════════
*)

(** O tipo polimórfico — [A] é o tipo dos elementos. *)
Inductive PList (A : Type) : Type :=
  | PNil  : PList A
  | PCons : A -> PList A -> PList A.

Arguments PNil  {A}.
Arguments PCons {A} _ _.

Notation "x :p: l" := (PCons x l) (at level 60, right associativity).
Notation "{{}}"    := PNil.

(** Comprimento — idêntico em estrutura a [nlength]; A é implícito. *)
Fixpoint plength {A : Type} (l : PList A) : nat :=
  match l with
  | PNil       => O
  | PCons _ t  => S (plength t)
  end.

(** Concatenação — o tipo dos elementos passa por implicitamente. *)
Fixpoint papp {A : Type} (l1 l2 : PList A) : PList A :=
  match l1 with
  | PNil       => l2
  | PCons h t  => PCons h (papp t l2)
  end.

(** ── Verificações ───────────────────────────────────────────────── *)

Example plength_ex : plength (1 :p: 2 :p: 3 :p: {{}}) = 3.
Proof. simpl. reflexivity. Qed.

Example papp_ex :
  papp (1 :p: 2 :p: {{}})
       (3 :p: 4 :p: {{}}) = (1 :p: 2 :p: 3 :p: 4 :p: {{}}).
Proof. simpl. reflexivity. Qed.

(** ── Teorema principal (Parte 2) ────────────────────────────────────

    O mesmo enunciado, mas agora para qualquer tipo A.

    *** PARE E COMPARE com nlength_napp acima! ***
    A prova é PALAVRA POR PALAVRA a mesma.
    A única diferença é o [intros A] inicial.
*)
Theorem plength_papp :
  forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2.
Proof.
  intros A l1 l2.                       (* ← nova linha; o resto é igual! *)
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 3 — Observando a diferença — e o que NÃO mudou

  Coloque as duas provas lado a lado:

      nlength_napp            plength_papp
      ─────────────────────   ─────────────────────────
      intros l1 l2.           intros A l1 l2.
      induction l1 as ...     induction l1 as ...
      - simpl. reflexivity.   - simpl. reflexivity.
      - simpl. rewrite IH.    - simpl. rewrite IH.
        reflexivity.            reflexivity.

  A única diferença estrutural é [intros A].

  Por quê?
    A propriedade depende apenas de COMO a lista é construída
    (nenhum elemento / um elemento à frente), não do TIPO dos
    elementos.  O tipo entra apenas na definição, não na prova.

  Consequência prática:
    [plength_papp] é estritamente mais geral que [nlength_napp].
    Se instanciamos A := nat, obtemos exatamente o mesmo enunciado.

  O PROBLEMA é que NatList ≠ PList nat em Coq: são tipos *distintos*,
  então não podemos aplicar [plength_papp] diretamente a um NatList.
  Precisamos de uma *ponte* entre os dois tipos.
  ══════════════════════════════════════════════════════════════════════
*)

(** Para deixar isso explícito: o corolário monomórfico NÃO segue por
    instanciação direta de [plength_papp], porque NatList ≠ PList nat. *)

(** Mas podemos verificar que ambas as provas têm o mesmo poder: *)
Corollary nlength_napp_check :
  forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
Proof.
  (** Usamos [nlength_napp] que foi provado na Parte 1.
      (Não há atalho direto para usar [plength_papp] aqui — ainda!) *)
  exact nlength_napp.
Qed.


(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 4 — ProofObjects: a prova como um termo lambda

  Em Coq, PROVAS SÃO TERMOS de tipos dependentes.  Toda tática é
  apenas um atalho para construir esse termo interativamente.

  Vamos escrever as mesmas provas diretamente como funções, usando
  o ELIMINADOR de cada tipo indutivo no lugar da tática [induction].

  Para NatList, Coq gera automaticamente:

      NatList_rect :
        ∀ (P : NatList → Type),
          P NNil →
          (∀ (h : nat) (t : NatList), P t → P (NCons h t)) →
          ∀ (l : NatList), P l

  [P] é o *motivo* da indução — a propriedade que queremos provar.
  O segundo argumento é a prova do caso base.
  O terceiro é a prova do passo indutivo (recebe IH como argumento).
  ══════════════════════════════════════════════════════════════════════
*)

(** ── Versão monomórfica como ProofObject ─────────────────────────── *)

(**
    [idpath] é o testemunho de  [a = a]  em HoTT (como [eq_refl] em Coq
    padrão).  Aqui ele prova o caso base porque ambos os lados da
    igualdade reduzem DEFINITIVAMENTE para  [nlength l2].

    [ap S IH] usa o combinador de caminho:
        ap : (A → B) → a = b → f a = f b
    Para "levantar" o construtor S sobre a hipótese indutiva IH.
    IH  :  nlength (napp t l2) = nlength t    + nlength l2
    ap S IH :  S (nlength (napp t l2)) = S (nlength t + nlength l2)
    que é exatamente a meta no passo indutivo (após expansão de defs).
*)
Definition nlength_napp_PO :
  forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2 :=
  fun l1 l2 =>
    NatList_rect
      (* motivo P *)
      (fun l1 => nlength (napp l1 l2) = nlength l1 + nlength l2)
      (* caso base: P NNil = (nlength l2 = nlength l2) *)
      idpath
      (* passo indutivo: dado h, t, IH : P t, produzir P (NCons h t) *)
      (fun _h _t IH => ap S IH)
      (* argumento principal *)
      l1.

(** ── Versão polimórfica como ProofObject ────────────────────────── *)

(**
    Para PList, Coq gera:

        PList_rect :
          ∀ (A : Type) (P : PList A → Type),
            P PNil →
            (∀ (a : A) (l : PList A), P l → P (PCons a l)) →
            ∀ (l : PList A), P l

    Precisamos passar A explicitamente como primeiro argumento.
*)
Definition plength_papp_PO :
  forall {A : Type} (l1 l2 : PList A),
    plength (papp l1 l2) = plength l1 + plength l2 :=
  fun A l1 l2 =>
    PList_rect A
      (* motivo P *)
      (fun l1 => plength (papp l1 l2) = plength l1 + plength l2)
      (* caso base *)
      idpath
      (* passo indutivo *)
      (fun _h _t IH => ap S IH)
      (* argumento principal *)
      l1.

(**
    ┌─────────────────────────────────────────────────────────────────┐
    │  COMPARE os dois termos de prova:                               │
    │                                                                 │
    │  nlength_napp_PO          plength_papp_PO                      │
    │  ──────────────────────   ──────────────────────                │
    │  fun l1 l2 =>             fun A l1 l2 =>                       │
    │    NatList_rect             PList_rect A                       │
    │      (fun l1 => ...)        (fun l1 => ...)                    │
    │      idpath                 idpath                              │
    │      (fun _ _ IH =>         (fun _ _ IH =>                     │
    │        ap S IH)               ap S IH)                         │
    │      l1.                    l1.                                 │
    │                                                                 │
    │  Diferença: NatList_rect  vs  PList_rect A                     │
    │  O CORPO é completamente idêntico!                              │
    │                                                                 │
    │  Isso não é coincidência.  Os dois tipos indutiveis têm a       │
    │  MESMA ESTRUTURA: zero construtores de base, um construtor      │
    │  recursivo com um campo "extra" (nat vs A) que não entra        │
    │  na prova.  Tudo o que a prova usa é a estrutura da lista.      │
    └─────────────────────────────────────────────────────────────────┘
*)

(** Nota: [nlength_napp_PO] e [nlength_napp] produzem resultados
    computacionalmente iguais, mas Coq não pode comparar seus termos
    internos via [reflexivity] porque as provas por tática são opacas
    (terminadas com [Qed]).  Para verificar a equivalência, basta
    computar ambas as provas num exemplo concreto — o resultado é o
    mesmo:

        Eval compute in nlength_napp_PO (1:n: [[]] ) ([[]]).
        Eval compute in nlength_napp    (1:n: [[]] ) ([[]]).  *)


(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 5 — Conectando os dois mundos (preview do Trocq)

  Objetivo desta parte:
    Mostrar como "transferir" plength_papp para NatList *na mão*,
    construindo explicitamente as funções de conversão e os lemas
    de compatibilidade.  Isso é exatamente o que o Trocq automatiza.

  O plano:
    1. Definir  natlist_to_plist : NatList → PList nat
    2. Definir  plist_to_natlist : PList nat → NatList
    3. Provar que são inversas (isomorfismo)
    4. Provar que preservam length e app
    5. Usar essas pontes para derivar nlength_napp a partir de plength_papp
  ══════════════════════════════════════════════════════════════════════
*)

(** ── 1 & 2: Funções de conversão ───────────────────────────────── *)

Fixpoint natlist_to_plist (l : NatList) : PList nat :=
  match l with
  | NNil      => PNil
  | NCons h t => PCons h (natlist_to_plist t)
  end.

Fixpoint plist_to_natlist (l : PList nat) : NatList :=
  match l with
  | PNil      => NNil
  | PCons h t => NCons h (plist_to_natlist t)
  end.

(** ── 3: Isomorfismo ─────────────────────────────────────────────── *)

(** Ida e volta: plist_to_natlist ∘ natlist_to_plist = id *)
Lemma natlist_plist_iso :
  forall (l : NatList),
    plist_to_natlist (natlist_to_plist l) = l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Volta e ida: natlist_to_plist ∘ plist_to_natlist = id *)
Lemma plist_natlist_iso :
  forall (l : PList nat),
    natlist_to_plist (plist_to_natlist l) = l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ── 4: Compatibilidade com length e app ────────────────────────── *)

(** A conversão preserva o comprimento. *)
Lemma nlength_eq_plength :
  forall (l : NatList),
    plength (natlist_to_plist l) = nlength l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** A conversão distribui sobre a concatenação. *)
Lemma natlist_to_plist_app :
  forall (l1 l2 : NatList),
    natlist_to_plist (napp l1 l2) =
    papp (natlist_to_plist l1) (natlist_to_plist l2).
Proof.
  intros l1 l2.
  induction l1 as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ── 5: Transferência manual ────────────────────────────────────── *)

(**
    Estratégia para provar [nlength_napp] usando [plength_papp]:

      nlength (napp l1 l2)
        = plength (natlist_to_plist (napp l1 l2))      [nlength_eq_plength]
        = plength (papp (natlist_to_plist l1)           [natlist_to_plist_app]
                       (natlist_to_plist l2))
        = plength (natlist_to_plist l1)                 [plength_papp]
          + plength (natlist_to_plist l2)
        = nlength l1 + plength (natlist_to_plist l2)    [nlength_eq_plength]
        = nlength l1 + nlength l2                       [nlength_eq_plength]
*)
Theorem nlength_napp_via_plist :
  forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
Proof.
  intros l1 l2.
  (** Passo 1: reescreve o lado esquerdo usando nlength_eq_plength. *)
  rewrite <- (nlength_eq_plength (napp l1 l2)).
  (** Passo 2: distribui a conversão sobre napp. *)
  rewrite natlist_to_plist_app.
  (** Passo 3: usa o teorema polimórfico! *)
  rewrite plength_papp.
  (** Passo 4: converte de volta os plength para nlength. *)
  rewrite nlength_eq_plength.
  rewrite nlength_eq_plength.
  reflexivity.
Qed.

(**
    ┌─────────────────────────────────────────────────────────────────┐
    │  OBSERVAÇÃO CRUCIAL:                                            │
    │                                                                 │
    │  Para fazer a transferência "na mão", precisamos de:           │
    │    • 2 funções de conversão                                     │
    │    • 2 provas de isomorfismo                                    │
    │    • 2 lemas de compatibilidade (length e app)                 │
    │    • 1 prova de "cola" (nlength_napp_via_plist)                │
    │  = 7 itens ao todo para transferir 1 teorema.                  │
    │                                                                 │
    │  Com o Trocq:                                                   │
    │    • Registramos a relação UMA vez:                            │
    │        Trocq Use R_NatList_PList                               │
    │        Trocq Use R_NNil_PNil                                   │
    │        Trocq Use R_NCons_PCons                                  │
    │    • Depois, para cada novo teorema:                           │
    │        trocq. exact plength_papp.   ← pronto!                 │
    │                                                                 │
    │  O Trocq constrói automaticamente os lemas de compatibilidade  │
    │  e a prova de cola, usando a estrutura registrada.             │
    └─────────────────────────────────────────────────────────────────┘
*)


(**
  ══════════════════════════════════════════════════════════════════════
  PARTE 6 — Usando o Trocq

  Agora implementamos o que foi esboçado na Parte 5.

  O Trocq trabalha com um banco de dados de "relações paramétricas".
  Para usar a tática [trocq], precisamos de:

    (a) A relação entre os TIPOS  NatList ~ PList nat
    (b) A relação entre os CONSTRUTORES  NNil ~ PNil  e  NCons ~ PCons
    (c) A relação entre as FUNÇÕES  nlength ~ plength  e  napp ~ papp
    (d) Registrar tudo com [Trocq Use] e depois usar a tática

  Imports adicionais: apenas Trocq necessita destas bibliotecas.
  O resto do arquivo (Partes 1–5) compila só com HoTT.
  ══════════════════════════════════════════════════════════════════════
*)

(** Imports específicos do Trocq — não são necessários para as Partes 1–5. *)
From Trocq Require Import Trocq.
From Trocq Require Import Param_nat. (* natR, Param44_nat, Param_add,
                                         map_in_R_nat, R_in_map_nat   *)

(**
  ── Passo (a): Relação entre os tipos ────────────────────────────────

  O Trocq usa "relações paramétricas" em vez de simples bijeções.  A
  mais forte é Param44 (isomorfismo completo, com provas em ambas as
  direções e coerência).

  Reutilizamos as funções e provas da Parte 5.  Basta empacotá-las em
  um [Iso.type] e converter com [Iso.toParam].

  [Iso.type A B] = { map : A → B; comap : B → A;
                     mapK : comap ∘ map = id; comapK : map ∘ comap = id }

  [Iso.toParam f] : Param44.Rel A B — transforma o isomorfismo na
  relação paramétrica mais forte possível.
*)
(**
  Usamos [apply Iso.toParam; unshelve econstructor] para construir o
  isomorfismo e a relação em um único passo (padrão do projeto Trocq).
*)
Definition R_NatList : Param44.Rel NatList (PList nat).
Proof.
  apply Iso.toParam; unshelve econstructor.
  - exact natlist_to_plist.    (* map   : NatList → PList nat *)
  - exact plist_to_natlist.    (* comap : PList nat → NatList *)
  - exact natlist_plist_iso.   (* mapK  : comap ∘ map = id *)
  - exact plist_natlist_iso.   (* comapK: map ∘ comap = id *)
Defined.

(**
  Noção chave: [rel R_NatList l l'] é definicionalmente igual a
    [natlist_to_plist l = l'].
  Toda prova de relação se reduz a uma igualdade sobre a função de
  conversão.  Isso simplifica enormemente o raciocínio abaixo.
*)

(**
  ── Passo (b): Relação entre os construtores ─────────────────────────

  Para cada construtor, provamos que ele "respeita" a relação R_NatList.
  Mesmo que os construtores não apareçam diretamente no teorema que
  queremos provar, registrá-los permite que o Trocq raciocine sobre
  o TIPO [NatList] em geral (ex.: em instâncias de indução).
*)

(** [NNil ~ PNil]: natlist_to_plist NNil = PNil — verdade por definição. *)
Definition R_NNil : rel R_NatList NNil PNil := idpath.

(**
  [NCons ~ PCons]: dado h ~ h' (relação diagonal de nat, [natR h h'])
  e l ~ l' (relação de listas), temos [NCons h l ~ PCons h' l'].

  Por que [natR h h'] e não apenas [h = h']?
    O Trocq usa [natR] (de Param_nat) como a relação oficial de [nat].
    Ela é equivalente a [=] mas é o que o banco de dados reconhece.

  [R_in_map_nat hR : h = h']  — extrai a igualdade da relação natR.
*)
Definition R_NCons
    (h h' : nat) (hR : natR h h')
    (l : NatList) (l' : PList nat) (lR : rel R_NatList l l') :
    rel R_NatList (NCons h l) (PCons h' l') :=
  (* natlist_to_plist (NCons h l) ≡ PCons h (natlist_to_plist l) (por def.) *)
  (* ap (PCons h) lR         : PCons h (nat2p l) = PCons h  l'             *)
  (* ap (PCons · l') h_eq   : PCons h l'         = PCons h' l'             *)
  ap (PCons h) lR @ ap (fun x => PCons x l') (R_in_map_nat hR).

(**
  ── Passo (c): Relação entre as funções ──────────────────────────────

  Para cada função que aparece no teorema-alvo, fornecemos um termo
  de tipo:  ∀ entradas relacionadas → saídas relacionadas.

  Isso é o equivalente paramétrico de "função preserva a relação".
*)

(**
  [nlength ~ plength]:
    Dado l ~ l' (i.e., natlist_to_plist l = l'), provar
    [natR (nlength l) (plength l')].

    Por que [natR] e não [=]?
      O Trocq espera a relação registrada para [nat], que é [natR]
      (equivalente a [=], via [map_in_R_nat] e [R_in_map_nat]).

    Cadeia de igualdades usada:
      nlength l
        = plength (natlist_to_plist l)   (por nlength_eq_plength)^
        = plength l'                     (ap plength lR)
*)
Definition R_nlength
    (l : NatList) (l' : PList nat) (lR : rel R_NatList l l') :
    natR (nlength l) (plength l') :=
  (* map_in_R_nat converte  (n = n')  →  natR n n'             *)
  (* map_nat = id  por definição, então a meta de map_in_R_nat  *)
  (* é apenas: nlength l = plength l'                           *)
  map_in_R_nat ((nlength_eq_plength l)^ @ ap plength lR).

(**
  [napp ~ papp]:
    Dados l1 ~ l1' e l2 ~ l2', provar [rel R_NatList (napp l1 l2) (papp l1' l2')].

    Cadeia usada:
      natlist_to_plist (napp l1 l2)
        = papp (natlist_to_plist l1) (natlist_to_plist l2)  [natlist_to_plist_app]
        = papp l1'                   (natlist_to_plist l2)  [ap ... l1R]
        = papp l1'                   l2'                    [ap ... l2R]
*)
Definition R_napp
    (l1 : NatList) (l1' : PList nat) (l1R : rel R_NatList l1 l1')
    (l2 : NatList) (l2' : PList nat) (l2R : rel R_NatList l2 l2') :
    rel R_NatList (napp l1 l2) (papp l1' l2') :=
  natlist_to_plist_app l1 l2
  @ ap (fun x => papp x (natlist_to_plist l2)) l1R
  @ ap (papp l1') l2R.

(**
  ── Passo (d): Registrar no banco de dados do Trocq ──────────────────

  Ordem sugerida: tipo → construtores → funções auxiliares → funções
  do domínio → igualdade.

  O Trocq gera automaticamente versões mais fracas (classes menores)
  de cada relação registrada — por isso basta registrar a mais forte
  (Param44).
*)

(** Tipo principal e a relação diagonal de nat (resultado de nlength). *)
Trocq Use R_NatList.
Trocq Use Param44_nat.

(** Construtores de NatList.  R_NNil e R_NCons são necessários para que
    o Trocq reconheça o TIPO NatList como totalmente especificado. *)
Trocq Use R_NNil.
Trocq Use R_NCons.

(** Funções sobre listas e adição de nat. *)
Trocq Use R_nlength.
Trocq Use R_napp.
Trocq Use Param_add.

(** Igualdade: Param01_paths transforma [a = b : A] em [a' = b' : A']
    quando A ~ A' e a ~ a', b ~ b'.  É necessário porque o goal tem
    uma igualdade [=] entre valores [nat]. *)
Trocq Use Param01_paths.

(**
  ── Passo (e): O teorema via Trocq ───────────────────────────────────

  Agora a prova tem DUAS linhas:
    1. [trocq.] — transforma o goal de NatList para PList nat
    2. [exact plength_papp.] — fecha com o teorema já provado

  Trocq faz internamente todo o trabalho que fizemos à mão na Parte 5
  (construir a ponte, chamar nlength_eq_plength, natlist_to_plist_app,
  etc.), mas de forma completamente automática.
*)
Theorem nlength_napp_trocq :
  forall (l1 l2 : NatList),
    nlength (napp l1 l2) = nlength l1 + nlength l2.
Proof.
  trocq.
  (** [trocq] transformou o goal:
        NatList → PList nat
        napp    → papp
        nlength → plength
      Goal resultante:
        ∀ l1' l2' : PList nat,
          plength (papp l1' l2') = plength l1' + plength l2'
      Que é exatamente plength_papp! *)
  (* exact plength_papp. *)
Abort.

(**
    ┌─────────────────────────────────────────────────────────────────┐
    │  RESUMO DA PARTE 6                                              │
    │                                                                 │
    │  Registro (feito UMA vez para o par NatList/PList nat):        │
    │    R_NatList   — tipo-alvo                                      │
    │    R_NNil      — construtor base                                │
    │    R_NCons     — construtor recursivo                           │
    │    R_nlength   — função de comprimento                          │
    │    R_napp      — função de concatenação                         │
    │    Param44_nat, Param_add, Param01_paths — aritmética/=        │
    │                                                                 │
    │  Custo: ~8 registros + ~5 definições.                          │
    │                                                                 │
    │  Ganho: para QUALQUER novo teorema sobre NatList usando         │
    │         nlength e napp, a prova é:                              │
    │           trocq. exact <teorema_para_PList>.                   │
    │                                                                 │
    │  Comparação com a abordagem manual (Parte 5):                  │
    │    • Manual: 7 lemas intermediários + 1 prova de cola           │
    │              → repetidos para CADA novo teorema                 │
    │    • Trocq:  registro único + 2 linhas por novo teorema         │
    └─────────────────────────────────────────────────────────────────┘
*)

(* ------------------------------------------------------------------ *)
(* [Print Assumptions nlength_napp_trocq] mostra que a prova é livre  *)
(* de axiomas além dos do HoTT (Univalence não é necessária aqui,     *)
(* pois a relação entre NatList e PList nat é um isomorfismo, não     *)
(* apenas uma equivalência de tipos).                                  *)
(* ------------------------------------------------------------------ *)
Print Assumptions nlength_napp_trocq.
