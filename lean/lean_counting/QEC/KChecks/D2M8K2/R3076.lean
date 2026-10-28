import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12304 = true := by
  decide +kernel

theorem tot12304 : totK PD2M8K2 D2M8K2.t12304 = [0, 0, 243144943764, 476375191120, 155648154900, 8462178015, 0, 0] := by
  decide +kernel

theorem rows12305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12305 = true := by
  decide +kernel

theorem tot12305 : totK PD2M8K2 D2M8K2.t12305 = [0, 117140089354, 349980337962, 317529886145, 80030919671, 3472187823, 0, 0] := by
  decide +kernel

theorem rows12306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12306 = true := by
  decide +kernel

theorem tot12306 : totK PD2M8K2 D2M8K2.t12306 = [0, 199115100626, 482257638552, 214572453701, 13258498675, 0, 0, 0] := by
  decide +kernel

theorem rows12307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12307 = true := by
  decide +kernel

theorem tot12307 : totK PD2M8K2 D2M8K2.t12307 = [0, 106287883958, 423642192875, 323693899629, 26434743981, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
