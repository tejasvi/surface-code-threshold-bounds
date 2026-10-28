import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8248 = true := by
  decide +kernel

theorem tot8248 : totK PD2M8K2 D2M8K2.t8248 = [0, 155154042726, 479838576626, 251387010987, 7896989526, 0, 0, 0] := by
  decide +kernel

theorem rows8249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8249 = true := by
  decide +kernel

theorem tot8249 : totK PD2M8K2 D2M8K2.t8249 = [0, 196294759147, 465596361324, 209811578828, 12264129317, 0, 0, 0] := by
  decide +kernel

theorem rows8250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8250 = true := by
  decide +kernel

theorem tot8250 : totK PD2M8K2 D2M8K2.t8250 = [123741341027, 337346542990, 293327867268, 139915414925, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows8251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8251 = true := by
  decide +kernel

theorem tot8251 : totK PD2M8K2 D2M8K2.t8251 = [192202735480, 452335673377, 226784285269, 17111991321, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
