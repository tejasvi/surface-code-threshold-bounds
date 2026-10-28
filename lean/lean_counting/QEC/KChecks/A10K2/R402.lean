import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1608 = true := by
  decide +kernel

theorem tot1608 : totK PA10K2 A10K2.t1608 = [0, 400532854576, 1694661299475, 2063570602362, 750894652211, 64029632433, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1609 = true := by
  decide +kernel

theorem tot1609 : totK PA10K2 A10K2.t1609 = [0, 0, 470928304773, 1825873871155, 1905713033984, 502781682620, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows1610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1610 = true := by
  decide +kernel

theorem tot1610 : totK PA10K2 A10K2.t1610 = [0, 514660386818, 1718097627735, 1810966675686, 667633703293, 76912880769, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1611 = true := by
  decide +kernel

theorem tot1611 : totK PA10K2 A10K2.t1611 = [0, 304062355366, 1541062777172, 2077971654872, 734569277985, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
