import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1476 = true := by
  decide +kernel

theorem tot1476 : totK PD2M8K2 D2M8K2.t1476 = [0, 0, 206460160045, 487679273915, 174486897994, 7611474319, 0, 0] := by
  decide +kernel

theorem rows1477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1477 = true := by
  decide +kernel

theorem tot1477 : totK PD2M8K2 D2M8K2.t1477 = [0, 104139918814, 359456233687, 351907031735, 71583367678, 946121569, 0, 0] := by
  decide +kernel

theorem rows1478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1478 = true := by
  decide +kernel

theorem tot1478 : totK PD2M8K2 D2M8K2.t1478 = [0, 158935106797, 439209103787, 277459853247, 29598161044, 0, 0, 0] := by
  decide +kernel

theorem rows1479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1479 = true := by
  decide +kernel

theorem tot1479 : totK PD2M8K2 D2M8K2.t1479 = [0, 152120965466, 449087765686, 276909946047, 21763210178, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
