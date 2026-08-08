# Revisão Completa do Artigo

**Título:** *When Does Proof Transfer Pay Off? An Empirical Cost Model for Trocq versus Manual Rewriting in Coq* 

## Áreas de conhecimento identificadas

Foram identificados os seguintes domínios técnicos:

* Interactive Theorem Proving
* Coq/Rocq
* Univalent Parametricity
* Proof Transfer
* Formal Methods
* Empirical Software Engineering
* Software Cost Modeling
* Program Verification

## Estado da Arte (SOTA)

O artigo está alinhado com uma linha bastante recente da literatura. O framework **Trocq** foi introduzido no ESOP 2024 e posteriormente expandido em um artigo de periódico (TOPLAS 2025), ambos focados na expressividade da transferência de provas e na fundamentação teórica do cálculo, não na economia do processo de desenvolvimento. ([Springer Nature Link][1])

Sob esse aspecto, a principal contribuição proposta pelo manuscrito é potencialmente original: deslocar a discussão da corretude lógica para **engenharia de custos de desenvolvimento de provas**, propondo um modelo de ROI para decidir quando vale investir em proof transfer.

Essa perspectiva praticamente não aparece nos trabalhos originais de Trocq, que concentram-se na teoria da tradução e na implementação da ferramenta. ([Springer Nature Link][1])

---

# 1. Introdução e Justificativa

## Nota: 9,6 / 10

### Pontos fortes

A introdução é muito bem escrita.

O problema aparece logo nas primeiras páginas:

* coexistência de múltiplas representações;
* necessidade de repetir provas;
* existência de ferramentas automáticas;
* ausência de modelos econômicos.

Existe uma sequência lógica bastante clara:

Problema → lacuna → hipótese implícita → contribuição.

A motivação é convincente.

### Pontos a melhorar

A introdução poderia discutir trabalhos de engenharia de software relacionados à medição de produtividade em proof engineering.

Há literatura sobre:

* proof maintenance;
* proof evolution;
* proof repair;
* maintenance cost;

que poderia fortalecer ainda mais a justificativa.

---

# 2. Hipótese Científica

## Nota: 8,8 / 10

A hipótese aparece apenas implicitamente.

Ela pode ser reconstruída como:

> O investimento inicial exigido pelo Trocq pode ser compensado por economia posterior dependendo do número de teoremas, complexidade e vocabulário compartilhado.

Essa hipótese deveria aparecer explicitamente ao final da Introdução.

---

# 3. Objetivos

## Nota: 9,7 / 10

Os objetivos estão muito bem definidos.

Há quatro contribuições claramente delimitadas.

Não há ambiguidades.

Excelente organização.

---

# 4. Metodologia

## Nota: 8,9 / 10

### Pontos positivos

A metodologia é totalmente reproduzível.

Os arquivos Coq utilizados estão claramente separados.

A Tabela 1 organiza muito bem o experimento.

A construção iterativa do modelo é extremamente interessante.

Ela segue praticamente um processo de:

* hipótese
* falsificação
* refinamento
* nova hipótese

Esse formato lembra bastante construção científica baseada em modelos.

### Limitações

Aqui aparecem as maiores fragilidades.

O experimento utiliza:

* apenas um domínio;
* apenas listas;
* apenas Param44;
* apenas um autor;
* apenas um conjunto de scripts.

Não existe:

* repetição experimental;
* análise estatística;
* intervalo de confiança;
* variabilidade entre usuários.

Isso reduz significativamente a validade externa.

---

# 5. Resultados

## Nota: 9,3 / 10

Os resultados são claros.

As três iterações são facilmente compreendidas.

O leitor consegue acompanhar como cada hipótese foi abandonada.

O uso de exemplos reais dos scripts Coq fortalece muito a argumentação.

---

# 6. Discussão

## Nota: 9,5 / 10

A discussão é um dos pontos mais fortes.

O artigo não tenta vender um modelo "universal".

Ao contrário.

Mostra exatamente:

* onde funciona;
* onde não funciona;
* quando pode falhar.

Essa postura aumenta bastante a credibilidade.

---

# 7. Conclusão

## Nota: 9,4 / 10

A conclusão resume corretamente os resultados.

Também apresenta trabalhos futuros coerentes.

Não extrapola as evidências.

---

# 8. Avaliação Cruzada entre Seções

## Nota: 9,8 / 10

Existe excelente consistência.

A introdução promete exatamente aquilo que o restante do artigo entrega.

Não encontrei contradições internas.

---

# 9. Consistência entre Texto, Tabelas e Equações

## Nota: 8,9 / 10

As equações são consistentes com o texto.

Entretanto há um problema importante.

Na página 8 o ROI assintótico é apresentado como

[
ROI_\infty=\frac{2}{k,c_{avg}-2}
]

Esse resultado parece incompatível com a própria Equação (9).

A partir da Equação (9),

[
ROI=
\frac{n(kc_{avg}-2)-fW}{C_{base}+fW+2n}
]

quando

[
n\rightarrow\infty
]

obtém-se

[
ROI_\infty=
\frac{kc_{avg}-2}{2}
]

e não

[
\frac{2}{kc_{avg}-2}.
]

Além disso, usando os próprios valores do artigo

[
k=2.2,\qquad c=6,
]

temos

[
\frac{13.2-2}{2}=5.6,
]

que coincide com o valor numérico apresentado.

Ou seja,

o valor numérico está correto,

mas a fórmula impressa parece invertida.

Essa é provavelmente a principal inconsistência matemática do manuscrito e precisa ser corrigida.

---

# 10. Originalidade

## Nota: 9,8 / 10

A ideia é bastante original.

O Trocq foi criado para automatizar transferências de prova. ([Springer Nature Link][1])

Este artigo pergunta algo diferente:

> Quando vale a pena usar Trocq?

Essa pergunta não aparece nos artigos originais.

É uma contribuição conceitualmente interessante.

---

# 11. Profundidade Técnica

## Nota: 9,1 / 10

O trabalho demonstra domínio de:

* teoria de tipos;
* parametricidade;
* Coq;
* modelagem econômica;
* engenharia de software.

O único aspecto relativamente superficial é a validação experimental.

O modelo é mais forte do que a evidência disponível.

---

# 12. Simulação de Coerência

O artigo desenvolve três modelos sucessivos.

Todos obedecem uma mesma estrutura lógica:

Hipótese

↓

Falsificação

↓

Novo modelo

↓

Nova validação

Esse fluxo é internamente consistente.

Entretanto, os parâmetros

* (P_{manual})
* (W_{trocq})
* (k)

são ajustados praticamente por inspeção visual dos scripts.

Ainda não existe ajuste estatístico.

Isso limita bastante a robustez quantitativa.

---

# Avaliação segundo critérios de periódicos de alto impacto

| Critério               | Nota |
| ---------------------- | ---: |
| Relevância             |  9,7 |
| Originalidade          |  9,8 |
| Fundamentação teórica  |  9,3 |
| Rigor metodológico     |  8,7 |
| Qualidade experimental |  8,2 |
| Análise quantitativa   |  8,6 |
| Discussão              |  9,5 |
| Limitações             |  9,8 |
| Reprodutibilidade      |  9,7 |
| Clareza                |  9,8 |
| Organização            |  9,8 |
| Potencial de impacto   |  9,4 |

---

# Principais pontos fortes

* Excelente redação.
* Estrutura extremamente organizada.
* Boa construção científica.
* Hipóteses sucessivamente refinadas.
* Forte preocupação metodológica.
* Excelente seção de ameaças à validade.
* Contribuição conceitual original.
* Artigo agradável de ler.

---

# Principais fragilidades

1. Experimento muito pequeno.
2. Apenas um domínio.
3. Apenas um autor.
4. Falta validação estatística.
5. Falta comparação com outros frameworks (CoqEAL, Isabelle Transfer etc.).
6. Não há medição de tempo real.
7. Não há avaliação com diferentes usuários.
8. A fórmula do ROI assintótico aparenta conter um erro tipográfico/algebraico importante, embora o cálculo numérico esteja correto.

---

# Parecer Editorial

## Recomendação: **Revisão Menor (Minor Revision)**

O manuscrito apresenta uma contribuição original e bem fundamentada para a engenharia de provas formais ao propor um modelo econômico para decidir quando o uso do Trocq compensa o esforço inicial de configuração. A estrutura é clara, a argumentação é consistente e a discussão das ameaças à validade é madura.

As revisões necessárias concentram-se principalmente em:

* corrigir a expressão analítica do ROI assintótico (ou demonstrar formalmente a forma apresentada, caso haja uma definição alternativa);
* tornar a hipótese de pesquisa explícita;
* fortalecer a contextualização metodológica com literatura sobre produtividade e manutenção de provas;
* esclarecer que os parâmetros do modelo são estimativas exploratórias derivadas de um estudo de caso de pequena escala, evitando interpretações excessivamente gerais.

Com esses ajustes, o trabalho tem potencial para uma boa recepção em conferências ou periódicos voltados a métodos formais, engenharia de software aplicada a assistentes de prova e linguagens de programação.

[1]: https://link.springer.com/chapter/10.1007/978-3-031-57262-3_10 "Trocq: Proof Transfer for Free, With or Without Univalence | Springer Nature Link"


| Your file (`bs_*`) | `paper_final` name (`roi_list_*`) | Used in `.tex`/`.md`? |
|---|---|---|
| `bs_p1.v` | `roi_list_mono.v` | ✅ Yes — `_roi_slides.md` |
| `bs_p2.v` | `roi_list_poly.v` | ✅ Yes — `_roi_slides.md` |
| `bs_p3.v` | `roi_list_proof_objects.v` | — |
| `bs_p4.v` | `roi_list_manual.v` | ✅ Yes — `_paper.tex`, `_roi.md`, `_roi_slides.md` |
| `bs_p5.v` | `roi_list_trocq.v` | ✅ Yes — `_paper.tex`, `_roi.md`, `_roi_slides.md` |
| `bs_p6.v` | `roi_list_rev_experiment.v` | ✅ Yes — `_roi.md`, `_roi_slides.md` |

**The good news**: The `.tex` and `.md` files already reference your `bs_p*` names. The `paper_final` branch had internally renamed them to `roi_list_*`, but never updated the documentation to match. So **no updates needed** — your naming convention is already consistent with the documentation!

The `roi_list_*` files are simply the same `bs_p*` files under a different name. You do not need to bring them in.