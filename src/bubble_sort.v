(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
(* end hide*)


(**
Este trabalho apresenta uma prova formal da correção do algoritmo de ordenação 
por borbulhamento (a função [bs] a seguir). A formalização foi feita no 
assistente de provas Coq. O assistente de provas Coq utiliza o sistema de 
Dedução Natural, o que o torna adequado para o desenvolvimento de atividades 
computacionais no curso de Lógica Computacional 1.

A estratégia geral da formalização é a seguinte: primeiro definimos [bubble], 
que executa uma única "passagem" do algoritmo de borbulhamento sobre uma lista; 
em seguida definimos [bs], o algoritmo bubble sort completo, como uma sequência 
de chamadas a [bubble]; por fim, provamos dois fatos sobre [bs] — que o 
resultado é uma lista ordenada ([bs_sorted]) e que o resultado é uma permutação 
da entrada ([bs_permuta]) — e combinamos os dois no teorema final [bs_correto]. 
Toda a dificuldade da prova está concentrada em entender exatamente *qual* 
propriedade [bubble] preserva a cada passo; o restante decorre de forma 
relativamente direta por indução. *)


(** Definição de [bubble]

Iniciaremos definindo a função [bubble] que recebe uma lista de naturais como 
argumento, e percorre esta lista comparando elementos consecutivos. Chamamos 
este processo de borbulhamento: a cada par de elementos vizinhos [x] e [y], 
se [x <= y] eles permanecem na mesma ordem e [bubble] continua comparando o 
restante da lista a partir de [y]; caso contrário, [x] e [y] trocam de lugar 
(o maior dos dois "salta" para a posição seguinte) e a comparação prossegue 
com o maior deles carregado adiante. O efeito líquido de uma chamada a 
[bubble] é, portanto, empurrar o maior elemento de cada par adjacente em 
direção ao final da lista, uma única vez. *)

Function bubble (l: list nat ) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::l =>
      if x <=? y
      then x::(bubble (y::l))
            else y::(bubble (x::l))
            end.
Proof.
  - auto.
  - auto.
Defined.

(** Observe que esta função não é estruturalmente recursiva porque, por 
exemplo, a lista [(x::l)] não é uma sublista da lista original [(x::y::l)] 
(o elemento [y] foi descartado, mas [x] foi reinserido na cabeça, então a 
recursão não ocorre apenas sobre uma "cauda" da lista original). Neste caso, 
utilizamos [Function] para construir esta função e precisamos fornecer a 
medida que decresce em cada chamada recursiva — aqui, o comprimento da lista, 
que diminui em exatamente um elemento a cada chamada recursiva, já que um 
elemento ([x] ou [y]) é consumido e colocado na posição final do resultado; 
além de provar (nas duas obrigações geradas pelo comando [Proof] acima) que 
esta medida efetivamente decresce a cada chamada recursiva; ambas as 
obrigações são triviais ([auto]) pois a lista recursiva tem sempre um 
elemento a menos que a lista de entrada do [match]. Por exemplo, 
[bubble (2::1::nil)] retorna a lista [(1::2::nil)]. *)

Eval compute in bubble (2::1::nil).

(**
  = 1 :: 2 :: nil
    : list nat
>>
*)

Eval compute in bubble (3::2::1::nil).

(**
  = 2 :: 1 :: 3 :: nil
    : list nat
>>
*)

(** Note que [bubble] não garante, em geral, que o elemento mínimo da lista 
vá parar na cabeça do resultado: o que [bubble] garante é uma propriedade 
*local*, a cada passo ele compara os dois primeiros elementos e "empurra" o 
maior deles para frente, repetindo o processo. Por isso [bubble (3::2::1::nil)] 
resulta em [2::1::3::nil] e não em [1::2::3::nil]: o [3], por ser maior que 
o [2], é deslocado para a direita logo na primeira comparação, e nunca mais é 
comparado com o [1]. Esta observação é crucial para toda a formalização: ela 
mostra que não é possível provar diretamente que a cabeça de [bubble l] é o 
mínimo de [l], e é o motivo pelo qual a propriedade de preservação de ordenação 
que provamos mais adiante ([bubble_preserves_sorted]) é enunciada de uma forma 
mais cuidadosa, sobre listas da forma [c::l] em que apenas a cauda [l] já está 
ordenada. *)

(** Definição de [bs]

A função principal, ou seja, o algoritmo bubble sort propriamente dito, é dada 
pela função [bs] abaixo que recebe uma lista de naturais como argumento:
*)

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => bubble (h::(bs l'))
  end.           
(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** O algoritmo [bs] ordena uma lista de forma recursiva: a cauda [l'] é 
ordenada recursivamente (obtendo [bs l']), supondo por hipótese de indução 
que esta chamada recursiva está correta, e, em seguida, a cabeça [h] é 
inserida nesta lista já ordenada por meio de uma única chamada de [bubble], 
que vai "borbulhando" [h] até a sua posição correta dentro de [bs l']. 
Esta é exatamente a estrutura de uma ordenação por inserção implementada 
com o auxílio de [bubble]: cada nova chamada de [bubble] tem a tarefa de 
inserir um único elemento novo ([h]) em uma lista que já se sabe 
ordenada ([bs l']). É precisamente esta leitura de [bs] que orienta a prova 
de [bs_sorted] mais adiante: ela é uma consequência quase imediata de um lema 
sobre [bubble] aplicado a uma lista da forma [c::l] com [l] ordenada. *)

(** Lemas auxiliares sobre [bubble]

Antes de provarmos as propriedades de [bs], precisamos de alguns resultados 
auxiliares sobre [bubble]. O primeiro deles nos diz que [bubble] preserva o 
tamanho da lista, isto é, [bubble] apenas reorganiza os elementos, sem 
remover nem duplicar nenhum deles. Este fato, embora simples, é um indício 
de que [bubble] de fato apenas permuta a lista de entrada (resultado este 
que será estabelecido de forma mais forte logo a seguir, pelo lema [bubble_perm]). 
A prova é por indução na própria definição de [bubble] 
(tática [functional induction]), que gera automaticamente um caso de prova 
para cada ramo do [match] e cada chamada recursiva de [bubble], com a 
hipótese de indução correspondente já disponível: *)

Lemma bubble_length: forall l, length (bubble l) = length l.
Proof.
  intro l.
  functional induction (bubble l).
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. assumption.
  - simpl. f_equal. assumption.
Qed.

(** O lema a seguir nos diz que a função [bubble] também gera uma permutação 
da entrada, ou seja, [bubble] não apenas preserva a quantidade de elementos, 
mas preserva também a multiplicidade de cada valor presente na lista. Este é 
o resultado que, mais tarde, dará origem a [bs_permuta] e, portanto, a metade 
do teorema final [bs_correto]. A estrutura da prova segue novamente o formato 
da definição de [bubble]: nos dois primeiros casos ([nil] e [x::nil]) a lista 
não é alterada, logo a permutação é a identidade ([Permutation_refl]); no 
terceiro caso, [x] é mantido na cabeça e a hipótese de indução (que afirma 
que [(y::l)] é permutação de [bubble (y::l)]) é "levantada" para a lista 
inteira por meio de [perm_skip]; no último caso, é preciso primeiro trocar 
[x] e [y] de posição (lema [perm_swap], que captura exatamente a troca que 
[bubble] realiza neste ramo) e, em seguida, aplicar a hipótese de indução da 
mesma forma que no caso anterior, compondo as duas permutações com [Permutation_trans]: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l.
  functional induction (bubble l).
  - apply Permutation_refl.
  - apply Permutation_refl.
  - apply perm_skip. assumption.
  - eapply Permutation_trans.
    + apply perm_swap.
    + apply perm_skip. assumption.
Qed.

(** Sabemos que aplicar a função [bubble] a uma lista qualquer, não 
necessariamente vai retornar uma lista ordenada (veja a observação acima 
sobre [bubble (3::2::1::nil)]), mas o lema [bubble_sorted] a seguir nos 
mostra que se a lista de entrada já está ordenada, ao aplicarmos a função 
[bubble], obtemos a mesma lista de volta — isto é, quando não há nenhuma 
inversão a corrigir, [bubble] é a identidade. Embora este lema não seja usado 
diretamente na prova de [bs_correto] (a propriedade de fato necessária é a 
mais geral [bubble_preserves_sorted], logo abaixo), ele é um resultado 
natural sobre [bubble] e ajuda a entender seu comportamento, além de ter sido 
um dos lemas propostos no enunciado original do trabalho. A prova segue de 
novo a estrutura de [bubble] via [functional induction]: nos dois primeiros 
casos o resultado é imediato; no terceiro caso, a hipótese [Sorted le (x::y::l)] 
fornece, por inversão, que [(y::l)] está ordenada, e a hipótese de indução 
conclui que [bubble (y::l) = (y::l)]; o último caso (em que [bubble] 
trocaria [x] e [y] de posição) é impossível quando a lista de entrada já está 
ordenada: a igualdade booleana [e0 : x <=? y = false] (extraída automaticamente 
do ramo do [if] pela tática [functional induction]) contradiz a hipótese 
[HdRel le x (y::l)] embutida em [Sorted le (x::y::l)], que afirma justamente 
que [x <= y]; essa contradição é obtida convertendo [e0] para a relação [y < x] 
(via [leb_complete_conv]) e fechada com [lia]: *)

Lemma bubble_sorted: forall l, Sorted le l -> bubble l = l.
Proof.
  intro l.
  functional induction (bubble l); intro Hs.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IHl0. inversion Hs. assumption.
  - exfalso. apply leb_complete_conv in e0.
    inversion Hs as [|? ? ? Hd]. inversion Hd. lia.
Qed.

(** O invariante central: [bubble] preserva a ordenação da cauda

Para provarmos que [bs] retorna uma lista ordenada, [bubble_sorted] não é 
suficiente: em [bs (h::l') = bubble (h::(bs l'))], nada garante a priori 
que [h] seja [<=] ou [>=] aos elementos de [bs l'], logo a lista [h::(bs l')] 
não está necessariamente ordenada antes da chamada a [bubble]. Precisamos, 
portanto, de um resultado mais geral sobre [bubble]: dado um elemento [c] 
qualquer (não necessariamente relacionado com os elementos de [l]) e uma 
lista [l] já ordenada, o resultado de [bubble (c::l)] também é uma lista 
ordenada. Este é o invariante essencial de [bubble] do ponto de vista do 
algoritmo bubble sort: ele preserva a ordenação da cauda [l], "infiltrando" 
o novo elemento [c] na posição correta a cada comparação, ainda que [c] 
não termine necessariamente na cabeça do resultado (como já vimos, 
[bubble] não garante isso). É este lema ([bubble_preserves_sorted], 
provado mais abaixo) que efetivamente torna [bs_sorted] uma consequência 
praticamente direta. Antes de prová-lo, precisamos de dois lemas auxiliares. *)

(** O primeiro lema auxiliar nos diz que se um elemento [a] é menor ou igual 
a todos os elementos de uma lista [l], então [a] também é menor ou igual a 
todos os elementos de [bubble l]. A ideia é que, como [bubble] apenas permuta 
os elementos de [l] (fato já estabelecido por [bubble_perm]), qualquer cota 
inferior válida para os elementos de [l] continua válida para os elementos 
de [bubble l], em particular para a cabeça de [bubble l] — que é exatamente 
o que a relação [HdRel le a (bubble l)] expressa, e que é a peça que falta 
para construir uma prova de [Sorted] via o construtor [Sorted_cons]. A prova 
analisa o resultado de [bubble l]: se for [nil], a relação [HdRel] vale 
trivialmente; se for [h::t], basta mostrar [a <= h], o que se obtém observando 
que [h] pertence a [bubble l] (por construção, é a cabeça da lista) e, 
por [bubble_perm] (usado em sua forma simétrica) e o lema [Permutation_in], 
também pertence a [l], onde a hipótese [H] garante [a <= h]: *)

Lemma bubble_HdRel_le: forall a l, (forall x, In x l -> a <= x) -> HdRel le a (bubble l).
Proof.
  intros a l H.
  destruct (bubble l) as [|h t] eqn:E.
  - constructor.
  - constructor. apply H. apply Permutation_in with (l:=bubble l).
    + apply Permutation_sym. apply bubble_perm.
    + rewrite E. left. reflexivity.
Qed.

(** O segundo lema auxiliar nos diz que se a lista [a::l] está ordenada, 
então [a] é menor ou igual a todos os elementos de [l] (e não apenas ao 
elemento imediatamente seguinte, que é tudo o que [HdRel] fornece diretamente). 
Isto decorre da transitividade de [le]: usamos a função da biblioteca padrão 
[Sorted_StronglySorted], que converte uma prova de [Sorted le (a::l)] em uma 
prova da versão "forte" [StronglySorted le (a::l)] — em que cada elemento é 
comparado com *todos* os elementos à sua direita, não apenas o seguinte, 
desde que se forneça uma prova de que [le] é transitiva (o que é resolvido 
por [lia]); da hipótese [StronglySorted le (a::l)], a relação [Forall (le a) l] 
(isto é, [a] relaciona-se com cada elemento de [l]) sai diretamente por inversão: *)

Lemma forall_le_a_l: forall a l, Sorted le (a::l) -> Forall (le a) l.
Proof.
  intros a l H.
  apply Sorted_StronglySorted in H.
  - inversion H. assumption.
  - unfold Relations_1.Transitive. intros. lia.
Qed.

(** Com os dois lemas auxiliares acima em mãos, podemos finalmente provar o 
resultado central: se [l] está ordenada, então [bubble (c::l)] também está 
ordenada, para qualquer [c]. A prova é por indução estrutural em [l] 
(não em [bubble], desta vez, pois precisamos generalizar sobre [c] a cada 
chamada recursiva da hipótese de indução, e a recursão de [bubble] mistura o 
papel de [c] e da cabeça de [l] de um passo para o outro):

- No caso [l = nil], [bubble (c::nil)] é, pela própria definição de [bubble] 
(ramo [x::nil]), igual a [c::nil], que está trivialmente ordenada.

- No caso [l = a::l''], sabemos por hipótese que [a::l''] está ordenada, 
o que fornece tanto [Sorted le l''] (por inversão) quanto, pelo lema [forall_le_a_l] 
provado acima, que [a] é [<=] a todos os elementos de [l''] (hipótese [Hall]). 
Reescrevendo [bubble (c::a::l'')] pela equação de [bubble] ([bubble_equation]), 
caímos no ramo de três elementos, que se bifurca conforme o resultado do teste [c <=? a]:

  + Se [c <= a] (extraído de [Hcomp] via [leb_complete]), o resultado é 
  [c :: bubble (a::l'')]. A cauda [bubble (a::l'')] está ordenada pela própria 
  hipótese de indução (instanciada com o elemento [a] no lugar de [c]). Falta 
  mostrar que [c] é [<=] à cabeça desse resultado: usamos [bubble_HdRel_le], 
  fornecendo como hipótese que [c] é [<=] a todos os elementos de [a::l'']; 
  isto vale porque [c <= a] (caso atual) e [a] é [<=] a todo elemento de [l''] 
  (hipótese [Hall]), e a relação [<=] é transitiva ([lia] resolve cada um dos 
  dois subcasos, conforme o elemento considerado seja o próprio [a] ou um elemento de [l'']).

  + Se [c > a] (extraído de [Hcomp] via [leb_complete_conv]), o resultado é 
  [a :: bubble (c::l'')]. A cauda [bubble (c::l'')] está ordenada novamente 
  pela hipótese de indução, desta vez instanciada com o mesmo [c]. Falta mostrar 
  que [a] é [<=] à cabeça desse resultado; usamos outra vez [bubble_HdRel_le], 
  agora fornecendo que [a] é [<=] a todos os elementos de [c::l'']: isto vale 
  porque [a <= c] (caso atual) e [a] é [<=] a todo elemento de [l''] (hipótese [Hall]).

Em ambos os subcasos, o argumento depende apenas de [a] (ou [c]) ser uma cota 
inferior para a lista *inteira* que está sendo borbulhada, e não de qual elemento 
especificamente acaba na cabeça do resultado — é exatamente esta independência 
que o lema [bubble_HdRel_le] captura e que torna a prova viável apesar de [bubble] 
não preservar a posição do mínimo. *)

Lemma bubble_preserves_sorted: forall l, Sorted le l -> forall c, Sorted le (bubble (c :: l)).
Proof.
  intro l.
  induction l as [|a l'' IH]; intros Hs c.
  - rewrite bubble_equation. constructor; constructor.
  - assert (Hsl'': Sorted le l'').
    { inversion Hs; assumption. }
    assert (Hall: Forall (le a) l'').
    { apply forall_le_a_l. assumption. }
    rewrite bubble_equation.
    destruct (c <=? a) eqn:Hcomp.
    + apply leb_complete in Hcomp.
      constructor.
      * apply IH; assumption.
      * apply bubble_HdRel_le. intros x Hin.
        destruct Hin as [Heq | Hin].
        -- subst. assumption.
        -- rewrite Forall_forall in Hall. specialize (Hall x Hin). lia.
    + apply leb_complete_conv in Hcomp.
      constructor.
      * apply IH; assumption.
      * apply bubble_HdRel_le. intros x Hin.
        destruct Hin as [Heq | Hin].
        -- subst. lia.
        -- rewrite Forall_forall in Hall. specialize (Hall x Hin). lia.
Qed.

(** ** Correção de [bs]: ordenação

Como consequência direta de [bubble_preserves_sorted], obtemos que [bs] retorna 
sempre uma lista ordenada. A prova é por indução estrutural em [l]: o caso [nil] 
é trivial; no caso [h::l'], a hipótese de indução [IH] nos dá exatamente que [bs l'] 
está ordenada, e basta então aplicar [bubble_preserves_sorted] com [c := h] e a 
lista ordenada [bs l'], já que, por definição, [bs (h::l') = bubble (h::(bs l'))]: *)

Lemma bs_sorted: forall l, Sorted le (bs l).
Proof.
  induction l as [|h l' IH].
  - simpl. constructor.
  - simpl. apply bubble_preserves_sorted. assumption.
Qed.

(** ** Correção de [bs]: permutação

O lema a seguir nos mostra que o algoritmo [bs] gera uma permutação da lista de 
entrada, como consequência de [bubble_perm]. A prova é também por indução 
estrutural em [l]: no caso [nil] a permutação é a identidade; no caso [h::l'], 
a hipótese de indução [IH] fornece que [l'] é permutação de [bs l']; daí, 
[h::l'] é permutação de [h::(bs l')] por [perm_skip] (que apenas preserva a 
cabeça [h] e aplica a permutação à cauda); finalmente, como [bs (h::l') = bubble (h::(bs l'))], 
usamos [bubble_perm] para obter que [h::(bs l')] é permutação de 
[bubble (h::(bs l'))] = [bs (h::l')], e compomos as duas permutações com [Permutation_trans]: *)

Lemma bs_permuta: forall l, Permutation l (bs l).
Proof.
  induction l as [|h l' IH].
  - simpl. apply Permutation_refl.
  - simpl. eapply Permutation_trans.
    + apply perm_skip. apply IH.
    + apply bubble_perm.
Qed.

(** ** Teorema final de correção

Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que 
estabelece que o algoritmo [bs] retorna uma permutação da lista de entrada 
que está ordenada. A prova é imediata: basta combinar os dois resultados 
já estabelecidos, [bs_sorted] e [bs_permuta], em uma conjunção: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
  intro l. split.
  - apply bs_sorted.
  - apply bs_permuta.
Qed.


(** Repositório: %\url{https://github.com/Carlos-E-Souza/projeto-analise-algoritmos}% *)