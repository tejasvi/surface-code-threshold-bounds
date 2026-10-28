import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6572 = true := by
  decide +kernel

theorem tot6572 : totK PA10K2 A10K2.t6572 = [0, 204967476529, 1004836347533, 1863351070118, 1436347643314, 264617521102, 11427838733, 0, 0, 0] := by
  decide +kernel

theorem rows6573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6573 = true := by
  decide +kernel

theorem tot6573 : totK PA10K2 A10K2.t6573 = [0, 442913129481, 1622772871520, 1941116001076, 666926286648, 52232171148, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6574 = true := by
  decide +kernel

theorem tot6574 : totK PA10K2 A10K2.t6574 = [0, 172943831038, 1320993746117, 2231539259670, 946306084880, 73656152536, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6575 = true := by
  decide +kernel

theorem tot6575 : totK PA10K2 A10K2.t6575 = [0, 0, 582284793847, 1985919810478, 1718568447468, 382905615962, 26172145312, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
