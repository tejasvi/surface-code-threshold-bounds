import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1480 = true := by
  decide +kernel

theorem tot1480 : totK PA10K2 A10K2.t1480 = [0, 0, 0, 0, 942168228249, 2408288917320, 1111778296304, 82168322541, 0, 0] := by
  decide +kernel

theorem rows1481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1481 = true := by
  decide +kernel

theorem tot1481 : totK PA10K2 A10K2.t1481 = [0, 0, 0, 0, 463946816893, 1809107014686, 1822717177081, 457185307923, 31193230065, 0] := by
  decide +kernel

theorem rows1482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1482 = true := by
  decide +kernel

theorem tot1482 : totK PA10K2 A10K2.t1482 = [0, 0, 0, 0, 761490283303, 2154489119627, 1477022511735, 239018474426, 6354603908, 0] := by
  decide +kernel

theorem rows1483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1483 = true := by
  decide +kernel

theorem tot1483 : totK PA10K2 A10K2.t1483 = [0, 0, 0, 0, 533333276147, 1835395860869, 1714337382223, 428456923279, 31009878902, 0] := by
  decide +kernel

end QECKChecks.A10K2
