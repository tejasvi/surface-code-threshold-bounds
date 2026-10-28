import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9128 = true := by
  decide +kernel

theorem tot9128 : totK PD2M8K2 D2M8K2.t9128 = [0, 0, 192291919781, 478259167355, 198005190760, 8908887416, 0, 0] := by
  decide +kernel

theorem rows9129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9129 = true := by
  decide +kernel

theorem tot9129 : totK PD2M8K2 D2M8K2.t9129 = [0, 0, 164706381029, 465592969587, 222045940272, 11625702507, 0, 0] := by
  decide +kernel

theorem rows9130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9130 = true := by
  decide +kernel

theorem tot9130 : totK PD2M8K2 D2M8K2.t9130 = [0, 0, 178895967708, 475808588393, 218865219733, 13797300897, 0, 0] := by
  decide +kernel

theorem rows9131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9131 = true := by
  decide +kernel

theorem tot9131 : totK PD2M8K2 D2M8K2.t9131 = [0, 0, 0, 297487444798, 444432574976, 77698857068, 1095107716, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
