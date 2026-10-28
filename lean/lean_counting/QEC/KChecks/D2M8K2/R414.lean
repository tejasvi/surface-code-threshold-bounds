import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1656 = true := by
  decide +kernel

theorem tot1656 : totK PD2M8K2 D2M8K2.t1656 = [0, 181674658392, 476610602229, 245460186089, 16795446989, 0, 0, 0] := by
  decide +kernel

theorem rows1657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1657 = true := by
  decide +kernel

theorem tot1657 : totK PD2M8K2 D2M8K2.t1657 = [0, 0, 274037889116, 504988498630, 120663845638, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1658 = true := by
  decide +kernel

theorem tot1658 : totK PD2M8K2 D2M8K2.t1658 = [0, 0, 212805980164, 482686569238, 181937965882, 7442000727, 0, 0] := by
  decide +kernel

theorem rows1659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1659 = true := by
  decide +kernel

theorem tot1659 : totK PD2M8K2 D2M8K2.t1659 = [0, 0, 176266447934, 476807904722, 222583254033, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
