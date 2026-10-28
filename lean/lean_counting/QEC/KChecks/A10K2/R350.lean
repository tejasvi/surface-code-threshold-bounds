import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1400 = true := by
  decide +kernel

theorem tot1400 : totK PA10K2 A10K2.t1400 = [0, 0, 0, 107710865134, 1197269879263, 2232806634080, 924022514040, 70910833822, 0, 0] := by
  decide +kernel

theorem rows1401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1401 = true := by
  decide +kernel

theorem tot1401 : totK PA10K2 A10K2.t1401 = [0, 0, 0, 395852129952, 1312094579737, 1863866970481, 984348464193, 160423754348, 5705019915, 0] := by
  decide +kernel

theorem rows1402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1402 = true := by
  decide +kernel

theorem tot1402 : totK PA10K2 A10K2.t1402 = [0, 0, 0, 380040883308, 1700753250294, 2089430331264, 740514433682, 57265082949, 0, 0] := by
  decide +kernel

theorem rows1403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1403 = true := by
  decide +kernel

theorem tot1403 : totK PA10K2 A10K2.t1403 = [0, 0, 0, 0, 584322376644, 2069217656675, 1894513429082, 396167668401, 12746179907, 0] := by
  decide +kernel

end QECKChecks.A10K2
