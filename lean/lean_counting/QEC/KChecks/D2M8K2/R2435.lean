import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9740 = true := by
  decide +kernel

theorem tot9740 : totK PD2M8K2 D2M8K2.t9740 = [0, 0, 214085470955, 486679023218, 171602664971, 7458616031, 0, 0] := by
  decide +kernel

theorem rows9741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9741 = true := by
  decide +kernel

theorem tot9741 : totK PD2M8K2 D2M8K2.t9741 = [0, 176984304571, 465580855005, 260566377993, 25447930073, 0, 0, 0] := by
  decide +kernel

theorem rows9742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9742 = true := by
  decide +kernel

theorem tot9742 : totK PD2M8K2 D2M8K2.t9742 = [0, 183967072867, 453932739383, 248266055197, 20028594331, 0, 0, 0] := by
  decide +kernel

theorem rows9743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9743 = true := by
  decide +kernel

theorem tot9743 : totK PD2M8K2 D2M8K2.t9743 = [0, 86446373630, 343248896747, 389113916296, 90864125835, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
