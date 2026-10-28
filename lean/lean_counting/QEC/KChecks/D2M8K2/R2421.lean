import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9684 = true := by
  decide +kernel

theorem tot9684 : totK PD2M8K2 D2M8K2.t9684 = [0, 0, 143944424046, 441511297640, 305694581596, 22999951857, 0, 0] := by
  decide +kernel

theorem rows9685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9685 = true := by
  decide +kernel

theorem tot9685 : totK PD2M8K2 D2M8K2.t9685 = [0, 0, 261067248956, 500761532278, 153074078159, 2939453538, 0, 0] := by
  decide +kernel

theorem rows9686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9686 = true := by
  decide +kernel

theorem tot9686 : totK PD2M8K2 D2M8K2.t9686 = [0, 0, 169240273379, 471163326370, 230716561970, 15976849042, 0, 0] := by
  decide +kernel

theorem rows9687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9687 = true := by
  decide +kernel

theorem tot9687 : totK PD2M8K2 D2M8K2.t9687 = [0, 0, 198124062836, 452493430298, 218138976606, 15039864920, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
