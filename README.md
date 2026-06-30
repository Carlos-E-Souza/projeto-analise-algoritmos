# projeto-analise-algoritmos
Repositório para a matéria de Projeto e Análise de Algoritmos do CIC-UNB

# Formalização do Algoritmo Bubble Sort

Este projeto apresenta uma prova formal da correção do algoritmo de ordenação **Bubble Sort** (ordenação por borbulhamento) utilizando o assistente de provas **Coq/Rocq**. O objetivo é garantir matematicamente que o algoritmo produz uma lista que está tanto ordenada quanto é uma permutação da lista original.

A formalização está **completa**: todos os lemas e o teorema final (`bs_correto`) estão provados, sem nenhum `Admitted` ou `Axiom` pendente. A prova foi verificada com `coqc` (compatível com Coq/Rocq 8.20), e a checagem `Print Assumptions bs_correto` confirma que o resultado depende apenas do núcleo lógico do sistema ("Closed under the global context").

## Estrutura do Projeto

A estrutura de arquivos do projeto e a finalidade de cada um são descritas abaixo:

- **`src/`**: Diretório contendo o código-fonte formalizado.
  - `bubble_sort.v`: Arquivo principal em Coq. Contém as definições das funções `bubble` e `bs`, os lemas auxiliares (`bubble_length`, `bubble_perm`, `bubble_sorted`, `bubble_HdRel_le`, `forall_le_a_l`, `bubble_preserves_sorted`), os lemas de correção (`bs_sorted`, `bs_permuta`) e o teorema final de correção (`bs_correto`).
- **`relatorio.pdf`**: Relatório técnico do projeto, em formato PDF, na raiz do repositório, descrevendo a estratégia de formalização, as dificuldades encontradas e as provas desenvolvidas.
- **`Makefile`**: Script de automação para compilação dos arquivos `.v` através do comando `make`.
- **`README.md`**: Este arquivo, contendo a descrição e instruções do projeto.
- **`LICENSE`**: Termos de licença do projeto.

## Como Utilizar

### Pré-requisitos
- [Coq/Rocq Proof Assistant](https://coq.inria.fr/) (versão 8.20)

### Comandos Principais
No terminal, na raiz do projeto, você pode executar:

- `make`: Compila os arquivos Coq (`.vo`).
- `make clean`: Remove os arquivos temporários gerados durante a compilação.

## Sobre a Formalização

A formalização utiliza o sistema de Dedução Natural e permite a extração de código certificado para linguagens como OCaml, Haskell e Scheme. O processo envolve:

1. Definir a função `bubble` (uma passagem do algoritmo de borbulhamento), via `Function` com uma medida de terminação sobre o comprimento da lista.
2. Definir a função `bs` (o algoritmo completo, via recursão estrutural sobre a lista de entrada).
3. Estabelecer o invariante central `bubble_preserves_sorted`: se `l` está ordenada, então `bubble (c::l)` também está ordenada, para qualquer `c` — note que `bubble` **não** garante que o mínimo da lista vá para a cabeça do resultado (apenas uma propriedade local a cada comparação), o que torna esse invariante mais sutil do que poderia parecer a princípio.
4. Provar que `bs` resulta em uma lista `Sorted` (`bs_sorted`), como consequência direta do invariante acima.
5. Provar que `bs` resulta em uma `Permutation` da entrada (`bs_permuta`), como consequência de `bubble_perm`.
6. Combinar os dois resultados no teorema final `bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l)`.