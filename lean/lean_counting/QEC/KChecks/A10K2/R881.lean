import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3524 = true := by
  decide +kernel

theorem tot3524 : totK PA10K2 A10K2.t3524 = [0, 0, 0, 0, 131446595523, 1409229575965, 2192761768610, 756326968162, 58519852657, 0] := by
  decide +kernel

theorem rows3525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3525 = true := by
  decide +kernel

theorem tot3525 : totK PA10K2 A10K2.t3525 = [0, 0, 433610675281, 1404868445336, 1268223320496, 370695050550, 617239282433, 625703209864, 138167057099, 6354482628] := by
  decide +kernel

theorem rows3526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3526 = true := by
  decide +kernel

theorem tot3526 : totK PA10K2 A10K2.t3526 = [0, 0, 519347338848, 1922020834062, 2075610339068, 593324602657, 44198948977, 0, 0, 0] := by
  decide +kernel

theorem rows3527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3527 = true := by
  decide +kernel

theorem tot3527 : totK PA10K2 A10K2.t3527 = [0, 0, 432469934381, 1764275321716, 2190923595194, 787654451821, 49918223929, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
