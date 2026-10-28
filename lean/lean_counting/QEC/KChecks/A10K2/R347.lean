import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1388 = true := by
  decide +kernel

theorem tot1388 : totK PA10K2 A10K2.t1388 = [0, 0, 0, 625907822805, 2133109977244, 1930454843725, 393836122401, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1389 = true := by
  decide +kernel

theorem tot1389 : totK PA10K2 A10K2.t1389 = [0, 0, 0, 606561488490, 1942973103076, 1794514773524, 554779139406, 41417404726, 0, 0] := by
  decide +kernel

theorem rows1390 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1390 = true := by
  decide +kernel

theorem tot1390 : totK PA10K2 A10K2.t1390 = [0, 0, 0, 500650867142, 1874452750465, 1966430573781, 516629720079, 31080743953, 0, 0] := by
  decide +kernel

theorem rows1391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1391 = true := by
  decide +kernel

theorem tot1391 : totK PA10K2 A10K2.t1391 = [0, 0, 0, 0, 781611578957, 2259580661161, 1582237547022, 260346270579, 6904928264, 0] := by
  decide +kernel

end QECKChecks.A10K2
