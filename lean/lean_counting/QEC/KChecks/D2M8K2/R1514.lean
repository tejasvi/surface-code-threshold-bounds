import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6056 = true := by
  decide +kernel

theorem tot6056 : totK PD2M8K2 D2M8K2.t6056 = [0, 0, 209977039779, 484190268365, 204991095810, 8130152497, 0, 0] := by
  decide +kernel

theorem rows6057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6057 = true := by
  decide +kernel

theorem tot6057 : totK PD2M8K2 D2M8K2.t6057 = [0, 168710648655, 366919442354, 223795420372, 120752043317, 11758933175, 0, 0] := by
  decide +kernel

theorem rows6058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6058 = true := by
  decide +kernel

theorem tot6058 : totK PD2M8K2 D2M8K2.t6058 = [0, 154865924962, 454397212841, 252451836518, 18064526750, 0, 0, 0] := by
  decide +kernel

theorem rows6059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6059 = true := by
  decide +kernel

theorem tot6059 : totK PD2M8K2 D2M8K2.t6059 = [0, 0, 287209233695, 505584247563, 86548476456, 1209030869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
