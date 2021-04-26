# Exact MUS Counter
Given an unsatisfiable set F = {f1, ..., fn} of Boolean clauses, i.e., a Boolean formula in CNF, this tool counts the number of Minimal Unsatisfiable Subsets (MUSes) of F. 
In particular, a subset N of F is an MUS of F iff N is unsatisfiable and every proper subset of N is satisfiable. Note that the minimality here is the set minimality and not the minimum cardinality. 

## Usage
`python3 counter.py <filename>`. For example, `python3 counter.py examples/m2_marco_input_76_100_58_refined.cnf`

To see all options, run `python3 counter.py -h`

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
