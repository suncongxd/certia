# Certia: Certifying Interface Automata for Cyber-Physical Systems #

* Component-based software development is widely considered as a promising approach on the design and development of cyber-physical systems.
* Interface automaton is a kind of light-weighted automata-theoretic formalism capturing temporal behaviors of component-based systems.

## Contributions ##

* A Coq-library of interface automata in purpose of certifying security properties of component-based CPS.
* Applications on compositional verification of information flow security for cyber-physical applications.

## Usage ##

* This library is developed with CoqIDE. 
* Use this implementation of interface automata by import IA.v and parser.v and construct your IAs as in examples.v.

## References

[1] Cong Sun, Qingsong Yao, Jianfeng Ma: Certia: Certifying Interface Automata for Cyber-Physical Systems. SMARTCOMP 2017: 1-3
[2] Cong Sun, Ning Xi, Jianfeng Ma: Enforcing Generalized Refinement-Based Noninterference for Secure Interface Composition. COMPSAC (1) 2017: 586-595
[3] Cong Sun, Ning Xi, Sheng Gao, Tao Zhang, Jinku Li, Jianfeng Ma: A Generalized Non-interference Based on Refinement of Interfaces. Journal of Computer Research and Development, 2015, 52(7): 1631-1641. (in Chinese)

## Author

* **Cong Sun** - *School of Cyber Engineering, Xidian University* - [E-mail: suncong AT xidian DOT edu DOT cn]

## License

* This library is licensed under the GPL 3.0 License. If it is used for academic publication, please cite our work [1][2].

## Change Log ##

This is certia v-0.4. The refinement-based noninterference verification is for the work [2]

* subset construction algorithm added: NewElement.v, NewState.v, subsetconst.v
* verification of SIR-GNNI and RRNI: refine.v