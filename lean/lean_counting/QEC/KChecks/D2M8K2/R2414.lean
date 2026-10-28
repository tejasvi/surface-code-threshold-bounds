import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9656 = true := by
  decide +kernel

theorem tot9656 : totK PD2M8K2 D2M8K2.t9656 = [0, 0, 206598744701, 488483516445, 181678001137, 8017150856, 0, 0] := by
  decide +kernel

theorem rows9657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9657 = true := by
  decide +kernel

theorem tot9657 : totK PD2M8K2 D2M8K2.t9657 = [0, 158714876269, 428227573655, 304320694990, 39737260836, 0, 0, 0] := by
  decide +kernel

theorem rows9658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9658 = true := by
  decide +kernel

theorem tot9658 : totK PD2M8K2 D2M8K2.t9658 = [0, 171189201866, 480289194319, 239514473092, 22448309949, 0, 0, 0] := by
  decide +kernel

theorem rows9659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9659 = true := by
  decide +kernel

theorem tot9659 : totK PD2M8K2 D2M8K2.t9659 = [0, 0, 293085951895, 527363532219, 91388309620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
