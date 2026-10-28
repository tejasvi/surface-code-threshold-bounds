import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t784 = true := by
  decide +kernel

theorem tot784 : totK PA10K2 A10K2.t784 = [0, 345735655366, 1616864336104, 1981202229009, 671071573519, 52620687920, 0, 0, 0, 0] := by
  decide +kernel

theorem rows785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t785 = true := by
  decide +kernel

theorem tot785 : totK PA10K2 A10K2.t785 = [0, 0, 681851331921, 2145065528793, 1582114208936, 268390082535, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t786 = true := by
  decide +kernel

theorem tot786 : totK PA10K2 A10K2.t786 = [0, 0, 484917940570, 1813343333273, 1918091403167, 504705399697, 31756067336, 0, 0, 0] := by
  decide +kernel

theorem rows787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t787 = true := by
  decide +kernel

theorem tot787 : totK PA10K2 A10K2.t787 = [0, 0, 528931767434, 1888979805585, 1949753613073, 504613163578, 31529138169, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
