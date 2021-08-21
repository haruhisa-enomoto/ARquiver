# AR quiver calculator
A GUI program to work with Auslander-Reiten quivers and compute various objects.

![image](https://media.discordapp.net/attachments/524877289213788171/878482371068981299/unknown.png?width=975&height=631)

(The Auslander-Reiten quiver of mod kQ for a quiver Q of type D5)

[exe file (9.7 MB) for Windows](https://github.com/haruhisa-enomoto/ARquiver/releases/download/v0.1.0/AR_quiver_calculator.exe) available.

## Contents

- [ARquiver.py](ARquiver.py): A module which does actual computation.
- [AR_quiver_calculator.py](AR_quiver_calculator.py): A GUI interface for [ARquiver.py](ARquiver.py).

## What can this do?
You can
- Input any finite translation quiver by clicking the canvas, or by using keyboard.
- Save and load your translation quiver.
- Import AR quiver from [String Applet](https://www.math.uni-bielefeld.de/~jgeuenich/string-applet/).

As for computations, so far, this can

- compute dim_k Hom(X,Y) for two indecomposables X and Y
- compute composition series of Hom functors

if your AR quiver is the AR quiver of some nice class of categories,
for example mod A for a finite-dimensional algebra A, or a Hom-finite triangulated category.
(See "Assumption" tab of the calculator for details.)


### Example
![Hom](https://media.discordapp.net/attachments/524877289213788171/878488400628432937/unknown.png)
The calculation of Hom(8,13) and Hom(-,13) and Hom(8,-) in the above D5 example.


In the near(?) future, I will add functions to compute torsion classes, tilting modules, wide subcategories, projective covers, and so on.

## Requirements

- exe file: Windows
- Python source codes: Python 3.7 or later.

## Author

[Haruhisa Enomoto](http://haruhisa-enomoto.github.io/), a postdoc, e-mail: the35883 [at] osakafu-u.ac.jp

## Changelog
- ver 0.1.0 - 2021-08-21: Initial version.
