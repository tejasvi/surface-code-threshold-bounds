import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t492 = true := by
  decide +kernel

theorem tot492 : totK PD2M8K2 D2M8K2.t492 = [0, 0, 245620398036, 497527514291, 152974181751, 8417083954, 0, 0] := by
  decide +kernel

theorem rows493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t493 = true := by
  decide +kernel

theorem tot493 : totK PD2M8K2 D2M8K2.t493 = [0, 154775387443, 376997445992, 282607001589, 70717872406, 3455941720, 0, 0] := by
  decide +kernel

theorem rows494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t494 = true := by
  decide +kernel

theorem tot494 : totK PD2M8K2 D2M8K2.t494 = [0, 154249029187, 439956862937, 282003739449, 30408478054, 0, 0, 0] := by
  decide +kernel

theorem rows495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t495 = true := by
  decide +kernel

theorem tot495 : totK PD2M8K2 D2M8K2.t495 = [0, 90259400040, 409099919034, 349819455054, 40917808043, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
