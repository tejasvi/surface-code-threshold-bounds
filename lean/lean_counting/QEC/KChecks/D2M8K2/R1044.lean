import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4176 = true := by
  decide +kernel

theorem tot4176 : totK PD2M8K2 D2M8K2.t4176 = [0, 175410780445, 443135726921, 272777061668, 29952589139, 0, 0, 0] := by
  decide +kernel

theorem rows4177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4177 = true := by
  decide +kernel

theorem tot4177 : totK PD2M8K2 D2M8K2.t4177 = [0, 164677750300, 464805497242, 270106987177, 21951593129, 0, 0, 0] := by
  decide +kernel

theorem rows4178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4178 = true := by
  decide +kernel

theorem tot4178 : totK PD2M8K2 D2M8K2.t4178 = [0, 0, 241201535924, 510314705542, 143548305954, 2304167554, 0, 0] := by
  decide +kernel

theorem rows4179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4179 = true := by
  decide +kernel

theorem tot4179 : totK PD2M8K2 D2M8K2.t4179 = [0, 0, 180542328616, 476971627278, 218660443788, 10135863696, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
