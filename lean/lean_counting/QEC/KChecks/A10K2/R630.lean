import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2520 = true := by
  decide +kernel

theorem tot2520 : totK PA10K2 A10K2.t2520 = [0, 553335258080, 1926008231676, 1957962770388, 543434629556, 31947994545, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2521 = true := by
  decide +kernel

theorem tot2521 : totK PA10K2 A10K2.t2521 = [0, 45277493360, 901995994735, 2230082192778, 1577526280685, 270532232827, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows2522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2522 = true := by
  decide +kernel

theorem tot2522 : totK PA10K2 A10K2.t2522 = [0, 436657417406, 1661420854031, 2101226633008, 866815473007, 73448919184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2523 = true := by
  decide +kernel

theorem tot2523 : totK PA10K2 A10K2.t2523 = [0, 361082162183, 1652406165365, 2221040303197, 785317682411, 36915635290, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
