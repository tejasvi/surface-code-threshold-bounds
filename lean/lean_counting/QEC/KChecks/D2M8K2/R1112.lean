import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4448 = true := by
  decide +kernel

theorem tot4448 : totK PD2M8K2 D2M8K2.t4448 = [0, 83203807696, 325039794888, 363614683698, 103216471608, 3884009855, 0, 0] := by
  decide +kernel

theorem rows4449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4449 = true := by
  decide +kernel

theorem tot4449 : totK PD2M8K2 D2M8K2.t4449 = [0, 177971042238, 451778368611, 268025155206, 28665014808, 0, 0, 0] := by
  decide +kernel

theorem rows4450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4450 = true := by
  decide +kernel

theorem tot4450 : totK PD2M8K2 D2M8K2.t4450 = [0, 159630077522, 452370955820, 276879868878, 20796637985, 0, 0, 0] := by
  decide +kernel

theorem rows4451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4451 = true := by
  decide +kernel

theorem tot4451 : totK PD2M8K2 D2M8K2.t4451 = [0, 0, 234499343998, 501228088810, 146083943090, 2304167554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
