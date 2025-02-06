# 选择公理及其等价命题的机器证明
选择公理是集合论里有关映射存在性的一条公理,最早于1904年由Zermelo提出,并用于对良序定理的证明,选择公理在现代数学中有很重要的作用,与许多深刻的数学结论有着十分密切的联系,没有选择公理,甚至无法确定两个集合能否比较元素的多少、非空集的积是否非空、线性空间是否一定有一组基、环是否一定有极大理想等等.选择公理有多个等价定理,包括Tukey引理、Hausdorf 极大原则、Zermelo 假定、Zorn 引理、良序定理等.拓扑学中重要的 Tychonoff 乘积定理即选择公理较为深刻的一个应用.
我们从选择公理出发,依次证明 Tukey引理、Hausdorff 极大原则、极大原则、Zermelo 假定、Zorn 引理和良序定理,再将选择公理视为一条定理,分别由 Tukey 引理、Zermelo 假定及良序定理证明选择公理,完成整个循环策略的证明,从而说明上述各命题与选择公理等价，这些命题的人工证明过程是标准的，散见于拓扑学或集合论的相关专著或教材中.
# 文件
证明基于Morse-Kelley 公理集论，它包括以下3个.v文件：
Pre_MK_Logic.v
MK_Structure1.v  (*Depends on Pre_MK_Logic.v *)
MK_Theorems1.v  (* Depends on MK_Structure1.v *)
选择公理及其等价命题的机器证明本身包括以下10个.v文件：
Basic_Definitions.v  (* Depends on MK_Theorems1.v *)
Tukey_Lemma.v  (* Depends on Basic_Definitions.v *)
Hausdorff_Maximal_Principle.v  (* Depends on Tukey_Lemma.v *)
Maximal_Principle.v  (* Depends on Hausdorff_Maximal_Principle.v *)
Zorn_Lemma.v  (* Depends on Maximal_Principle.v *)
Wellordering_Theorem.v  (* Depends on Zorn_Lemma.v *)
WO_Proof_AC.v  (* Depends on Wellordering_Theorem.v *)
Zermelo_Postulate.v  (* Depends on Maximal_Principle.v *)
Zermelo_Proof_AC.v  (* Depends on Zermelo_Postulate.v *)
Tukey_Proof_AC.v  (* Depends on Tukey_Lemma.v *)
# Authors
This project is implemented by Wensheng Yuwsyu@bupt.edu.cn、Tianyu Sun、Yaoshun Fu、Sheng Yan、Si Chen、Ce Zhang.
# Relevant Papers & Books
Yu, W., Sun, T., Fu, Y.: A Machine Proof System for Axiomatic Set Theory (in Chinese). Science Press, Beijing (2020)
