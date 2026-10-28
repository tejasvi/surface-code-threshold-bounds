import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9836 = true := by
  decide +kernel

theorem tot9836 : totK PD2M8K2 D2M8K2.t9836 = [0, 0, 302097341694, 507934481841, 92189076785, 1069412848, 0, 0] := by
  decide +kernel

theorem rows9837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9837 = true := by
  decide +kernel

theorem tot9837 : totK PD2M8K2 D2M8K2.t9837 = [0, 166903323934, 414439447133, 263560416976, 61034555092, 2814597007, 0, 0] := by
  decide +kernel

theorem rows9838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9838 = true := by
  decide +kernel

theorem tot9838 : totK PD2M8K2 D2M8K2.t9838 = [0, 192415365441, 464153878797, 240134148068, 17239952341, 0, 0, 0] := by
  decide +kernel

theorem rows9839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9839 = true := by
  decide +kernel

theorem tot9839 : totK PD2M8K2 D2M8K2.t9839 = [0, 55785187685, 322276205914, 417845871810, 94848876011, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
