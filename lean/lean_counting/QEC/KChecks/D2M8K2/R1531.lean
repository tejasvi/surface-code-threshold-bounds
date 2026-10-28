import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6124 = true := by
  decide +kernel

theorem tot6124 : totK PD2M8K2 D2M8K2.t6124 = [185771158094, 467808856241, 219217514422, 14004961759, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6125 = true := by
  decide +kernel

theorem tot6125 : totK PD2M8K2 D2M8K2.t6125 = [69729640418, 325417631309, 412334429128, 92788249007, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6126 = true := by
  decide +kernel

theorem tot6126 : totK PD2M8K2 D2M8K2.t6126 = [33295144018, 336779724357, 477169312985, 63627352739, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6127 = true := by
  decide +kernel

theorem tot6127 : totK PD2M8K2 D2M8K2.t6127 = [193357925688, 469357943714, 234645336380, 20265910454, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
