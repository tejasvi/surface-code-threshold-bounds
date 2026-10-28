import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3624 = true := by
  decide +kernel

theorem tot3624 : totK PD2M8K2 D2M8K2.t3624 = [0, 196278082761, 479793456439, 230705642026, 13541533318, 0, 0, 0] := by
  decide +kernel

theorem rows3625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3625 = true := by
  decide +kernel

theorem tot3625 : totK PD2M8K2 D2M8K2.t3625 = [0, 92402001151, 416117498125, 359196111859, 48966023071, 0, 0, 0] := by
  decide +kernel

theorem rows3626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3626 = true := by
  decide +kernel

theorem tot3626 : totK PD2M8K2 D2M8K2.t3626 = [0, 0, 209278852904, 474202010169, 217956418172, 13604428459, 0, 0] := by
  decide +kernel

theorem rows3627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3627 = true := by
  decide +kernel

theorem tot3627 : totK PD2M8K2 D2M8K2.t3627 = [0, 99785162053, 339098850136, 357646752358, 94815257398, 1409560813, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
