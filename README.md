# Exact MUS Counter
Given an unsatisfiable set F = {f1, ..., fn} of Boolean clauses, i.e., a Boolean formula in CNF, this tool counts the number of Minimal Unsatisfiable Subsets (MUSes) of F. 
In particular, a subset N of F is an MUS of F iff N is unsatisfiable and every proper subset of N is satisfiable. Note that the minimality here is the set minimality and not the minimum cardinality. 

## Usage
`python3 counter.py <filename>`. For example, `python3 counter.py examples/m2_marco_input_76_100_58_refined.cnf`

To see all options, run `python3 counter.py -h`

## Input Formats
The tools supports counting for "plain" MUS instances and "group" MUS instances. 

### "Plain" MUS
The input for plain MUS counting is the standard [DIMACS cnf format](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SATLINK____DIMACS). The DIMACS files should have the extension ".cnf". An example .cnf file can be found in `./examples/test.cnf`:

```
p cnf 2 5
1 0
-1 0
2 0
-2 0
-1 -2 0
```

In this example, there are three MUSes: {1,2}, {3,4}, and {1,3,5}, where the numbers are 1-based indices of individual clauses. 

### "Group" MUS
In the group MUS settings, the input clauses are divided into a set `H` of "hard clauses" and a set `S` of "soft clauses". A group MUS is a subset `N` of `S` such that `N \cup H` is unsatisfiable, and for every proper subset `N'` of `N` the set `N' \cup H` is satisfiable. The group MUS instances are defined in the "group DIMACS format", i.e., files with the extension .gcnf. The header has the format "p gcnf \<variables\> \<clauses\> \<soft_clauses\>". Furthermore, every hard clauses is marked with {0} at the start of the line, and every soft clauses is marked with {k} where k is a positive integer. An example .gcnf file can be found in `./examples/test.gcnf`:
 
```
p gcnf 2 5 4
{0} 1 0
{1} -1 0
{2} 2 0
{3} -2 0
{4} 1 2 0
```

Here, there are two group MUSes: {1} and {2,3}, where the number are the 1-based indices of the soft clauses. 

## Third Party Tools
We distribute linux-compiled binaries of three (publicly available) tools: [ganak](https://github.com/meelgroup/ganak), [rime](https://github.com/jar-ben/rime), and [uwrmaxsat](https://github.com/marekpiotrow/UWrMaxSat). The binaries (and the licenses) can be found in the directory `./tools`. In case you want to optimize the computation (or notice some problems), we suggest you to download the tools and rebuild the binaries on your own. 

## Related Tools
To the best of our knowledge, our MUS counting approach is the very first (and currently the only) "exact" counting approach that does not rely on explicit MUS enumeration; the alternative contemporary approach is to simply enumerate all MUSes via an MUS enumeration tool. However, since there can be up to exponentially many MUSes w.r.t. |F|, the complete enumeration is often practically intractable.
In case that the complete MUS enumeration is tractable, you should use our contemporary MUS enumerator [UNIMUS](https://github.com/jar-ben/unimus).
Finally, you can also try our probabilistic approximate counter [AMUSIC](https://github.com/jar-ben/amusic).


## Citation
A paper that introduces our counting approach was accepted to CAV 2021 (to appear). If you use the tool, please, cite our paper:

```
@inproceedings{BendikMeelCAV2021,
  author    = {Jaroslav Bend{\'{\i}}k and
               Kuldeep S. Meel},
  title     = {Counting Minimal Unsatisfiable Subsets},
  booktitle = {CAV},
  year      = {2021 (to appear)}
}
```

## Contact
In case of any questions of problems, please contact me at xbendik=at=gmail.com
