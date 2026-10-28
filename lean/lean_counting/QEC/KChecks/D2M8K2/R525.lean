import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2100 = true := by
  decide +kernel

theorem tot2100 : totK PD2M8K2 D2M8K2.t2100 = [0, 0, 159924027347, 466079644060, 256660964351, 15994294308, 0, 0] := by
  decide +kernel

theorem rows2101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2101 = true := by
  decide +kernel

theorem tot2101 : totK PD2M8K2 D2M8K2.t2101 = [0, 0, 0, 264499284069, 485141559509, 113621371868, 2160984415, 0] := by
  decide +kernel

theorem rows2102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2102 = true := by
  decide +kernel

theorem tot2102 : totK PD2M8K2 D2M8K2.t2102 = [0, 0, 105929799503, 395241974526, 318663508218, 59560272709, 2770420231, 0] := by
  decide +kernel

theorem rows2103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2103 = true := by
  decide +kernel

theorem tot2103 : totK PD2M8K2 D2M8K2.t2103 = [0, 0, 187184548164, 448682589160, 246335235211, 18585984037, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
