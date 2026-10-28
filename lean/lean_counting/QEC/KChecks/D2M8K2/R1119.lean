import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4476 = true := by
  decide +kernel

theorem tot4476 : totK PD2M8K2 D2M8K2.t4476 = [0, 46802713861, 218527177936, 425169654758, 211900960401, 9332673987, 0, 0] := by
  decide +kernel

theorem rows4477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4477 = true := by
  decide +kernel

theorem tot4477 : totK PD2M8K2 D2M8K2.t4477 = [0, 180297322710, 450263819161, 250649122354, 23126203384, 0, 0, 0] := by
  decide +kernel

theorem rows4478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4478 = true := by
  decide +kernel

theorem tot4478 : totK PD2M8K2 D2M8K2.t4478 = [0, 192376299835, 474323471526, 224833264445, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows4479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4479 = true := by
  decide +kernel

theorem tot4479 : totK PD2M8K2 D2M8K2.t4479 = [0, 4159293103, 297294336671, 481101184205, 101076935595, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
