import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4420 = true := by
  decide +kernel

theorem tot4420 : totK PD2M8K2 D2M8K2.t4420 = [0, 0, 0, 216292186023, 499570031876, 157873893913, 5159868635, 0] := by
  decide +kernel

theorem rows4421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4421 = true := by
  decide +kernel

theorem tot4421 : totK PD2M8K2 D2M8K2.t4421 = [0, 0, 167887236175, 420847442510, 312149082554, 44052902185, 0, 0] := by
  decide +kernel

theorem rows4422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4422 = true := by
  decide +kernel

theorem tot4422 : totK PD2M8K2 D2M8K2.t4422 = [0, 0, 178057066267, 482964084077, 243865964373, 9491231608, 0, 0] := by
  decide +kernel

theorem rows4423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4423 = true := by
  decide +kernel

theorem tot4423 : totK PD2M8K2 D2M8K2.t4423 = [0, 0, 0, 279945847753, 494443085743, 128806175340, 4031931762, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
