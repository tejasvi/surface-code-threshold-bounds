import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1292 = true := by
  decide +kernel

theorem tot1292 : totK PD2M8K2 D2M8K2.t1292 = [157474047746, 464443704941, 264534732431, 18697754474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1293 = true := by
  decide +kernel

theorem tot1293 : totK PD2M8K2 D2M8K2.t1293 = [0, 287826707791, 507547047135, 105494437037, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows1294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1294 = true := by
  decide +kernel

theorem tot1294 : totK PD2M8K2 D2M8K2.t1294 = [172185291182, 388261674959, 245842178767, 82921407731, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows1295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1295 = true := by
  decide +kernel

theorem tot1295 : totK PD2M8K2 D2M8K2.t1295 = [161313671031, 446659637162, 279192673661, 22577236149, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
