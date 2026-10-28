import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15776 = true := by
  decide +kernel

theorem tot15776 : totK PD2M8K2 D2M8K2.t15776 = [0, 0, 86220738987, 323459332984, 386359223056, 103175889104, 4030866388, 0] := by
  decide +kernel

theorem rows15777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15777 = true := by
  decide +kernel

theorem tot15777 : totK PD2M8K2 D2M8K2.t15777 = [0, 0, 177212523815, 464983906420, 254311895001, 22176305422, 0, 0] := by
  decide +kernel

theorem rows15778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15778 = true := by
  decide +kernel

theorem tot15778 : totK PD2M8K2 D2M8K2.t15778 = [0, 0, 178308376453, 479583305193, 251504743103, 13539187914, 0, 0] := by
  decide +kernel

theorem rows15779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15779 = true := by
  decide +kernel

theorem tot15779 : totK PD2M8K2 D2M8K2.t15779 = [0, 0, 0, 273219061888, 505398103158, 119670163079, 1268739303, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
