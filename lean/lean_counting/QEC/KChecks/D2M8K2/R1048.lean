import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4192 = true := by
  decide +kernel

theorem tot4192 : totK PD2M8K2 D2M8K2.t4192 = [0, 0, 102015507908, 386180883738, 332614604095, 64425505987, 2532065704, 0] := by
  decide +kernel

theorem rows4193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4193 = true := by
  decide +kernel

theorem tot4193 : totK PD2M8K2 D2M8K2.t4193 = [0, 0, 174560063152, 444313145642, 267979871349, 24795922139, 0, 0] := by
  decide +kernel

theorem rows4194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4194 = true := by
  decide +kernel

theorem tot4194 : totK PD2M8K2 D2M8K2.t4194 = [0, 0, 164196490766, 462741263848, 270805474034, 19732413170, 0, 0] := by
  decide +kernel

theorem rows4195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4195 = true := by
  decide +kernel

theorem tot4195 : totK PD2M8K2 D2M8K2.t4195 = [0, 0, 0, 236388931355, 498701824420, 133790101228, 2348340425, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
