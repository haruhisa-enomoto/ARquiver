# AR quiver calculator
A GUI program to work with Auslander-Reiten quivers and compute various objects.

![image](https://media.discordapp.net/attachments/524877289213788171/879642217411657738/unknown.png?width=890&height=630)

(The Auslander-Reiten quiver of the cluster category of type A3)

- [exe file (9.7 MB) for Windows](https://github.com/haruhisa-enomoto/ARquiver/releases/download/v0.2.1/ARquiver_calculator.exe) available.
- [app file for Mac](https://github.com/haruhisa-enomoto/ARquiver/releases/download/v0.2.1/ARquiver_calculator.app.zip) available.

## Contents

- [ARquiver.py](ARquiver.py): A module which does actual computation.
- [ARquiver_calculator.py](ARquiver_calculator.py): A GUI interface for [ARquiver.py](ARquiver.py).
- [examples](/examples/): A folder which contains some AR quivers (mod kQ and cluster categories of some Dynkin types)

## What can this do?
You can
- Input any finite translation quiver by clicking the canvas, or by using keyboard.
- Save and load your translation quiver.
- Import AR quiver from [String Applet](https://www.math.uni-bielefeld.de/~jgeuenich/string-applet/).

As for computations, so far, this can

- Compute dim_k Hom(X,Y) for two indecomposables X and Y.
- Compute composition series of Hom functors.

If your category is a triangulated category, then this can

- Compute shift functors, Serre functors
- List all objects which are self Ext^n-orthogonal for designated values n.
(e.g. list all maximal Ext^1-orthogonal = cluster tilting objects if your category is 2-CY)

(See "Help -> Assumptions" of the calculator for details on supported categories.)

In the near(?) future, I will add functions to compute torsion classes, (tau)-tilting modules, wide subcategories, projective covers, cluster-tilting, and so on.

**If you want some functions, then please contact me!**

### Example

- The calculation of Hom.

![Hom](https://media.discordapp.net/attachments/524877289213788171/879642561017425960/unknown.png)

- The calculation of shift functors.

![Shift](https://media.discordapp.net/attachments/524877289213788171/879642504033599528/unknown.png)

- The calculation of all maximal Ext-orthogonal objects.

![Ortho](https://media.discordapp.net/attachments/524877289213788171/879642680630595594/unknown.png?width=941&height=630)


## Requirements

- exe file: Windows
- app file: Mac
- Python source codes: Python 3.7 or later and [PySimpleGUI](https://pysimplegui.readthedocs.io/en/latest/)

## Author

[Haruhisa Enomoto](http://haruhisa-enomoto.github.io/), a postdoc, e-mail: the35883 [at] osakafu-u.ac.jp

## Changelog

- ver 0.2.1 - 2021-09-02:
  - Correct some typos and add Mac app file.

- ver 0.2.0 - 2021-08-24:
  - Improve graphics and layouts.
  - Improve open, save and import functions. Import from String Applet now preserves locations of vertices.
  - Add calculations on triangulated categories (shift, maximal Ext-orthogonals)

- ver 0.1.0 - 2021-08-21: Initial version.
