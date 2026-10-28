import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5104 = true := by
  decide +kernel

theorem tot5104 : totK PA10K2 A10K2.t5104 = [0, 307423764049, 1531526966071, 2250680752434, 966065817057, 82986860969, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5105 = true := by
  decide +kernel

theorem tot5105 : totK PA10K2 A10K2.t5105 = [0, 0, 422512481810, 1725238677447, 2138488032207, 761348918285, 56143165367, 0, 0, 0] := by
  decide +kernel

theorem rows5106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5106 = true := by
  decide +kernel

theorem tot5106 : totK PA10K2 A10K2.t5106 = [0, 0, 542859681491, 1906796574418, 1905049081992, 513641873730, 31712524204, 0, 0, 0] := by
  decide +kernel

theorem rows5107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5107 = true := by
  decide +kernel

theorem tot5107 : totK PA10K2 A10K2.t5107 = [0, 0, 112467149459, 975365518489, 2124921749360, 1460499938787, 250945179464, 7047025452, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
