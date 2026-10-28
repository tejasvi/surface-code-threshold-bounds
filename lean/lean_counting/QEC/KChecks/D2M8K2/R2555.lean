import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10220 = true := by
  decide +kernel

theorem tot10220 : totK PD2M8K2 D2M8K2.t10220 = [0, 0, 197803698360, 455043952296, 198578834260, 13514095470, 0, 0] := by
  decide +kernel

theorem rows10221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10221 = true := by
  decide +kernel

theorem tot10221 : totK PD2M8K2 D2M8K2.t10221 = [0, 0, 207816970630, 493754458816, 189783423730, 5265834820, 0, 0] := by
  decide +kernel

theorem rows10222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10222 = true := by
  decide +kernel

theorem tot10222 : totK PD2M8K2 D2M8K2.t10222 = [0, 0, 168200593445, 475610669761, 236751396258, 7681674495, 0, 0] := by
  decide +kernel

theorem rows10223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10223 = true := by
  decide +kernel

theorem tot10223 : totK PD2M8K2 D2M8K2.t10223 = [0, 94308289763, 280772975571, 354252600299, 181217832986, 13322746131, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
