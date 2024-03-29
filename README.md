# US-Rule
This repo hosts the code for paper **"US-Rule: Discovering Utility-driven Sequential Rules", ACM Transactions on Knowledge Discovery from Data, Gengsen Huang, Wensheng Gan, Jian Weng, and Philip S. Yu, 2023**.

## Requirements
Java programming language.

## Running the program
A simple way is to run MainTestUSRule_saveToFile.java.

## Benchmarks
- The data format used is the same as in the file data.txt. That is, different positive integers represent different terms. In addition, "-1" is used as the itemset separator and "-2" is used as the sequence separator.
- Additional datasets can be accessed from [SPMF](http://www.philippe-fournier-viger.com/spmf/index.php?link=datasets.php).

## Introduction
The US-Rule algorithm is proposed to efficiently mine high-utility sequential rules. To improve the efficiency on dense and long sequence datasets, four tighter upper bounds (LEEU, REEU, LERSU, RERSU) and their corresponding pruning strategies (LEEUP, REEUP, LERSUP, RERSUP) are designed. Besides, US-Rule also utilizes rule estimated utility co-occurrence pruning strategy (REUCP) to avoid meaningless computation and rule estimated utility recomputing pruning strategy (REURP) to deal with sparse datasets.

## Citation
If this article or code useful for your project, please refer to
```xml
@article{huang2023us,
  title={{US-Rule}: Discovering Utility-driven Sequential Rules},
  author={Huang, Gengsen and Gan, Wensheng and Weng, Jian and Yu, Philip S.},
  journal={ACM Transactions on Knowledge Discovery from Data},
  volume={17},
  number={1},
  pages={1--22},
  year={2023},
  publisher={ACM New York, NY, USA}
}

```

## Notes
If there are any questions, please contact us (Email: hgengsen@gmail.com).
