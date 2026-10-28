import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1348 = true := by
  decide +kernel

theorem tot1348 : totK PD2M8K2 D2M8K2.t1348 = [0, 124699839690, 421703727629, 307539814050, 38624066990, 0, 0, 0] := by
  decide +kernel

theorem rows1349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1349 = true := by
  decide +kernel

theorem tot1349 : totK PD2M8K2 D2M8K2.t1349 = [0, 175201767390, 447070504986, 266476321028, 25022329187, 0, 0, 0] := by
  decide +kernel

theorem rows1350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1350 = true := by
  decide +kernel

theorem tot1350 : totK PD2M8K2 D2M8K2.t1350 = [0, 145600847910, 452144563627, 292962762987, 22504783920, 0, 0, 0] := by
  decide +kernel

theorem rows1351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1351 = true := by
  decide +kernel

theorem tot1351 : totK PD2M8K2 D2M8K2.t1351 = [0, 0, 222403015718, 483588784326, 155596511182, 4811815119, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
