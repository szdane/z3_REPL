# SMT Solver with Z3 for Integer and Boolean Logic

This project implements an **SMT solver REPL** using the **Z3 theorem prover** in **OCaml**. It supports **integer and Boolean variables**, **logical and arithmetic expressions**, and **quantifiers**.

## 📌 Features
- Supports **arithmetic expressions** (`+`, `-`, `*`, `/`, `<=`, `>=`, `=`, `!=`)
- Supports **Boolean logic** (`and`, `or`, `not`)
- Supports **quantifiers** (`forall x:Int (...)`, `exists b:Bool (...)`)
- Uses **Z3** to check **satisfiability (SAT/UNSAT)** of formulas
- Interactive input for **checking logical statements**
- **Correctly infers types** of variables based on declarations (`Int` or `Bool`)

---

## 🛠 Installation

### Install **OCaml**
Ensure you have **OCaml** and **Dune** installed:

```sh
opam install ocaml dune
```

### Install **Z3**
The project requires **Z3 bindings for OCaml**:

```sh
opam install z3
```

### Build the Project
```sh
dune build
```

### Run the Interactive Solver
```sh
cd _build/default
./main.exe
```

---

## 🎯 Usage Examples

### **Basic Arithmetic**
```
> 3 + 5 <= 10
Z3 Expression: (<= (+ 3 5) 10)
Result: SAT
```

### **Boolean Logic**
```
> not true
Z3 Expression: (not true)
Result: UNSAT
```

### **Using Quantifiers**
```
> forall x:Int (x + 3 <= 10)
Z3 Expression: (forall ((x Int)) (<= (+ x 3) 10))
Result: SAT
```

### **Mixed Quantifiers**
```
> forall x:Int, exists b:Bool (x > 3 or not b)
Z3 Expression: (forall ((x Int)) (exists ((b Bool)) (or (> x 3) (not b))))
Result: SAT
```

---

## 📜 Syntax Reference

| Feature             | Syntax Example                     | Description |
|---------------------|----------------------------------|-------------|
| **Addition**       | `3 + 5`                          | Arithmetic addition |
| **Subtraction**    | `10 - 2`                         | Arithmetic subtraction |
| **Multiplication** | `4 * 7`                          | Multiplication |
| **Division**       | `8 / 2`                          | Division |
| **Inequality**     | `x <= 10`, `x >= 3`              | Comparison |
| **Equality**       | `x = y`, `x != y`               | Equality and inequality |
| **Logical AND**    | `x and y`                        | Boolean AND |
| **Logical OR**     | `x or y`                         | Boolean OR |
| **Negation**       | `not x`                          | Boolean NOT |
| **Forall Quantifier** | `forall x:Int (x > 3)`       | Universal quantification |
| **Exists Quantifier** | `exists b:Bool (not b)`     | Existential quantification |
