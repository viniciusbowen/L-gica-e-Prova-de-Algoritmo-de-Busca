# Correção do Algoritmo de Ordenação por Inserção Binária

Projeto final da disciplina **Lógica Computacional 1 (2026/1)** — Universidade de Brasília.

Formalização e prova de correção do algoritmo de ordenação por inserção binária (`binsertion_sort`) utilizando o assistente de provas **Rocq**.

## Participantes

| Nome              | Matrícula |
| ----------------- | --------- |
| Daniel da Cunha Pereira Luz | 211055540 |
| Thiago Veras Rodrigues Queiroz | 211055370 |
| Vinícius Bowen | 180079239 |

---

## Como rodar

### Pré-requisitos

- Ubuntu 22.04 ou superior (ou WSL2 no Windows)
- curl

### 1. Instalar o opam

```bash
sudo apt install opam
```

### 2. Inicializar o opam

```bash
opam init
# Responda 'y' para ambas as perguntas
eval $(opam env)
```

### 3. Instalar o Rocq (Coq)

```bash
opam install coq
eval $(opam env)
```

Verifique a instalação:

```bash
coqc --version
```

### 4. Compilar

```bash
coqc binsertion_sort.v
```

Se não houver erros, todas as provas foram verificadas com sucesso.
