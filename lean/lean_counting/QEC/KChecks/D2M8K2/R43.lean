import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t172 = true := by
  decide +kernel

theorem tot172 : totK PD2M8K2 D2M8K2.t172 = [0, 93518571537, 386635762168, 360501932941, 60262322099, 1242138600, 0, 0] := by
  decide +kernel

theorem rows173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t173 = true := by
  decide +kernel

theorem tot173 : totK PD2M8K2 D2M8K2.t173 = [0, 0, 254691750488, 485320417616, 131794023411, 3569676519, 0, 0] := by
  decide +kernel

theorem rows174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t174 = true := by
  decide +kernel

theorem tot174 : totK PD2M8K2 D2M8K2.t174 = [0, 92342479873, 237932243318, 342068575367, 194282623263, 16939352947, 0, 0] := by
  decide +kernel

theorem rows175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t175 = true := by
  decide +kernel

theorem tot175 : totK PD2M8K2 D2M8K2.t175 = [0, 174846244669, 483257283299, 233643136956, 11038245751, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
