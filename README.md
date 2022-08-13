# AR quiver calculator
A GUI program to work with Auslander-Reiten quivers and compute various objects.

![image](https://cdn.discordapp.com/attachments/524877289213788171/1007891731703943168/unknown.png)

(The Auslander-Reiten quiver of the representation of D5 quiver, and a torsion class of it)

- [exe file (9.4 MB) for Windows](https://github.com/haruhisa-enomoto/ARquiver/releases/download/v0.3.0/ARquiver_calculator.exe) available.
- For Mac: to be appeared soon, or directly using python.

## Contents

- [ARquiver.py](ARquiver.py): A module which does actual computation.
- [ARquiver_calculator.py](ARquiver_calculator.py): A GUI interface for [ARquiver.py](ARquiver.py).
- [examples](/examples/): A folder which contains some AR quivers

## What can this do?

### 1. Input AR quiver

Input AR quiver of your module category or triangulated category as follows:
- Input any finite translation quiver by clicking the canvas, or by using keyboard.
- Save and load your translation quiver.
- Import AR quiver from [String Applet](https://www.math.uni-bielefeld.de/~jgeuenich/string-applet/).

Basic Input          |  Import from String Applet (Double Triangle)
:-------------------------:|:-------------------------:
![](https://cdn.discordapp.com/attachments/524877289213788171/1007893449502113852/unknown.png)  |  ![](https://cdn.discordapp.com/attachments/524877289213788171/1007895483554992138/unknown.png)

### 2. Compute Hom and Ext^1

Select X and Y, then this computes the dimensions of Hom(X, Y) and Ext^1(X, Y).

2-dim Hom in mod k(D5)   |  1-dim Ext in A3 cluster category
:-------------------------:|:-------------------------:
![](https://cdn.discordapp.com/attachments/524877289213788171/1007896233454612571/unknown.png)  |  ![](https://cdn.discordapp.com/attachments/524877289213788171/1007897271528075284/unknown.png)

### 3. For a module category, compute various subcategories.

This computes the following classes of the module categories: torsion(-free) classes, wide subcategories, ICE-closed subcategories (closed under Images, Cokernels, Extennsions), IE-closed subcategories (closed under Images, Extensions), etc.

Also, for a selected subcategory C, this computes all the Ext-projective (injective) objects.

 A torsion class and its projs in A4 quiver | One of 1051 IE-closed subcats of some alg
:-------------------------:|:-------------------------:
![](https://cdn.discordapp.com/attachments/524877289213788171/1007900187106234368/unknown.png)  |  ![](https://cdn.discordapp.com/attachments/524877289213788171/1007901782200025189/unknown.png)


### 4. For a triangulated category, compute shift functors and maximal Ext-orthogonals.

 Applying shift in A3 cluter cat | There're 182 maximal Ext^1-rigid objs in D5 cluter cat
:-------------------------:|:-------------------------:
![](https://cdn.discordapp.com/attachments/524877289213788171/1007902867484590130/unknown.png)  |  ![](https://cdn.discordapp.com/attachments/524877289213788171/1007903351888949278/unknown.png)


**If you want some functions, then please contact me!**


## Requirements

- exe file: Windows
- app file: Mac
- Python source codes: Python 3.7 or later and [PySimpleGUI](https://pysimplegui.readthedocs.io/en/latest/)

## Author

[Haruhisa Enomoto](http://haruhisa-enomoto.github.io/), a postdoc, e-mail: henomoto [at] omu.ac.jp

## Changelog

- ver 0.3.0 - 2022-08-13:
  - Improve UI (fit size, display copies of AR quivers for other tabs, etc)
  - Add the following features:
    - Compute Ext^1
    - Compute various subcategories and their Ext-projective (injective) objects in them.

- ver 0.2.1 - 2021-09-02:
  - Correct some typos and add Mac app file.

- ver 0.2.0 - 2021-08-24:
  - Improve graphics and layouts.
  - Improve open, save and import functions. Import from String Applet now preserves locations of vertices.
  - Add calculations on triangulated categories (shift, maximal Ext-orthogonals)

- ver 0.1.0 - 2021-08-21: Initial version.
