import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16172 = true := by
  decide +kernel

theorem tot16172 : totK PD2M8K2 D2M8K2.t16172 = [0, 165180638508, 450913853459, 280063382200, 30300958707, 0, 0, 0] := by
  decide +kernel

theorem rows16173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16173 = true := by
  decide +kernel

theorem tot16173 : totK PD2M8K2 D2M8K2.t16173 = [0, 154398851678, 451847063795, 278944204617, 19885278580, 0, 0, 0] := by
  decide +kernel

theorem rows16174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16174 = true := by
  decide +kernel

theorem tot16174 : totK PD2M8K2 D2M8K2.t16174 = [0, 0, 227836807032, 497491609544, 168459349833, 7233348802, 0, 0] := by
  decide +kernel

theorem rows16175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16175 = true := by
  decide +kernel

theorem tot16175 : totK PD2M8K2 D2M8K2.t16175 = [0, 79515775218, 278980626740, 383660581754, 129199299999, 6017336459, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
