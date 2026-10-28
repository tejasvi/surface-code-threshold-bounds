import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9028 = true := by
  decide +kernel

theorem tot9028 : totK PD2M8K2 D2M8K2.t9028 = [0, 0, 279337611728, 517359492146, 91109674966, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9029 = true := by
  decide +kernel

theorem tot9029 : totK PD2M8K2 D2M8K2.t9029 = [0, 157129989792, 390749583213, 270952073714, 78570741537, 3821179711, 0, 0] := by
  decide +kernel

theorem rows9030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9030 = true := by
  decide +kernel

theorem tot9030 : totK PD2M8K2 D2M8K2.t9030 = [0, 164257180446, 438412796588, 266547280841, 22001230685, 0, 0, 0] := by
  decide +kernel

theorem rows9031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9031 = true := by
  decide +kernel

theorem tot9031 : totK PD2M8K2 D2M8K2.t9031 = [0, 92232705550, 355835374259, 373809045589, 73455126285, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
