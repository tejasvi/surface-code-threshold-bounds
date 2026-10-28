import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4468 = true := by
  decide +kernel

theorem tot4468 : totK PD2M8K2 D2M8K2.t4468 = [0, 37052073317, 208556122558, 417654562640, 228371181520, 15906108236, 0, 0] := by
  decide +kernel

theorem rows4469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4469 = true := by
  decide +kernel

theorem tot4469 : totK PD2M8K2 D2M8K2.t4469 = [0, 200233537379, 469678940582, 201728703400, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows4470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4470 = true := by
  decide +kernel

theorem tot4470 : totK PD2M8K2 D2M8K2.t4470 = [0, 139701420044, 449795712102, 273908168700, 21697398164, 0, 0, 0] := by
  decide +kernel

theorem rows4471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4471 = true := by
  decide +kernel

theorem tot4471 : totK PD2M8K2 D2M8K2.t4471 = [0, 0, 270243565307, 511173177951, 102757338632, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
