import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1328 = true := by
  decide +kernel

theorem tot1328 : totK PD2M8K2 D2M8K2.t1328 = [89913192444, 353049426558, 380582281221, 78672312948, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows1329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1329 = true := by
  decide +kernel

theorem tot1329 : totK PD2M8K2 D2M8K2.t1329 = [0, 234957825607, 477843328809, 161512705053, 9465717894, 0, 0, 0] := by
  decide +kernel

theorem rows1330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1330 = true := by
  decide +kernel

theorem tot1330 : totK PD2M8K2 D2M8K2.t1330 = [151250617986, 404669818746, 290301429143, 66872740403, 2552562263, 0, 0, 0] := by
  decide +kernel

theorem rows1331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1331 = true := by
  decide +kernel

theorem tot1331 : totK PD2M8K2 D2M8K2.t1331 = [169398958782, 446212373349, 276206460983, 29436346227, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
