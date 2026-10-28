import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15748 = true := by
  decide +kernel

theorem tot15748 : totK PD2M8K2 D2M8K2.t15748 = [0, 0, 0, 212640393589, 469245389389, 210328282884, 14517393958, 0] := by
  decide +kernel

theorem rows15749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15749 = true := by
  decide +kernel

theorem tot15749 : totK PD2M8K2 D2M8K2.t15749 = [0, 0, 132970761498, 345789160361, 291259157775, 116584054271, 8935385149, 0] := by
  decide +kernel

theorem rows15750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15750 = true := by
  decide +kernel

theorem tot15750 : totK PD2M8K2 D2M8K2.t15750 = [0, 0, 190463954495, 475243350254, 195421088364, 10749708610, 0, 0] := by
  decide +kernel

theorem rows15751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15751 = true := by
  decide +kernel

theorem tot15751 : totK PD2M8K2 D2M8K2.t15751 = [0, 0, 66946647745, 366205839568, 382174465078, 55768010100, 1310166938, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
