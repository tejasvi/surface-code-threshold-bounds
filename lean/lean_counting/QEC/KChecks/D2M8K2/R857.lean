import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3428 = true := by
  decide +kernel

theorem tot3428 : totK PD2M8K2 D2M8K2.t3428 = [0, 169153994513, 474358010044, 242262823500, 11581424576, 0, 0, 0] := by
  decide +kernel

theorem rows3429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3429 = true := by
  decide +kernel

theorem tot3429 : totK PD2M8K2 D2M8K2.t3429 = [0, 179096388524, 454793984625, 220349539340, 16861767938, 0, 0, 0] := by
  decide +kernel

theorem rows3430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3430 = true := by
  decide +kernel

theorem tot3430 : totK PD2M8K2 D2M8K2.t3430 = [104347864613, 318691539042, 373940560370, 120285912933, 3896246883, 0, 0, 0] := by
  decide +kernel

theorem rows3431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3431 = true := by
  decide +kernel

theorem tot3431 : totK PD2M8K2 D2M8K2.t3431 = [184591332416, 473361506506, 237140366255, 16630841668, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
