import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7728 = true := by
  decide +kernel

theorem tot7728 : totK PD2M8K2 D2M8K2.t7728 = [0, 0, 0, 148952904728, 444493744230, 230661846979, 15675192952, 0] := by
  decide +kernel

theorem rows7729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7729 = true := by
  decide +kernel

theorem tot7729 : totK PD2M8K2 D2M8K2.t7729 = [0, 0, 0, 0, 301774474888, 444756441360, 78695789340, 1021600638] := by
  decide +kernel

theorem rows7730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7730 = true := by
  decide +kernel

theorem tot7730 : totK PD2M8K2 D2M8K2.t7730 = [0, 0, 0, 170010058057, 386554854616, 233279182466, 66289824629, 3552795014] := by
  decide +kernel

theorem rows7731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7731 = true := by
  decide +kernel

theorem tot7731 : totK PD2M8K2 D2M8K2.t7731 = [0, 0, 0, 234745935235, 473787474468, 187393304616, 8518091041, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
