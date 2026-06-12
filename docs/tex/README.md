# Compilación del documento

Este proyecto utiliza LaTeX con BibTeX y la clase IEEEtran.

## Requisitos

Tener instalada una distribución de LaTeX que incluya `latexmk`:

- TeX Live (Linux)
- MacTeX (macOS)
- MiKTeX (Windows)

## Compilar

Desde la carpeta actual del proyecto:

```bash
latexmk -pdf equivalencia-dependiente-de-contexto.tex
```


## Limpiar

Para eliminar los archivos temporales generados durante la compilación y conservar únicamente el PDF:


```bash
latexmk -c
```


