import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7552 = true := by
  decide +kernel

theorem tot7552 : totK PD2M8K2 D2M8K2.t7552 = [0, 0, 213243640016, 491721116685, 196260590546, 3643890547, 0, 0] := by
  decide +kernel

theorem rows7553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7553 = true := by
  decide +kernel

theorem tot7553 : totK PD2M8K2 D2M8K2.t7553 = [0, 176559373540, 385999492579, 240641613502, 98919342311, 6511038260, 0, 0] := by
  decide +kernel

theorem rows7554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7554 = true := by
  decide +kernel

theorem tot7554 : totK PD2M8K2 D2M8K2.t7554 = [0, 165747318986, 442441662557, 285826553851, 30233312356, 0, 0, 0] := by
  decide +kernel

theorem rows7555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7555 = true := by
  decide +kernel

theorem tot7555 : totK PD2M8K2 D2M8K2.t7555 = [0, 104271980057, 428382161584, 346024959497, 30489321144, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
