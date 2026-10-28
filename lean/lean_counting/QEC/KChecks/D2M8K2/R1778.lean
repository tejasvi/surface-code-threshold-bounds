import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7112 = true := by
  decide +kernel

theorem tot7112 : totK PD2M8K2 D2M8K2.t7112 = [0, 0, 199528405160, 473546851715, 212165740078, 13309748521, 0, 0] := by
  decide +kernel

theorem rows7113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7113 = true := by
  decide +kernel

theorem tot7113 : totK PD2M8K2 D2M8K2.t7113 = [0, 0, 204563001930, 465247305846, 195330929141, 12064174497, 0, 0] := by
  decide +kernel

theorem rows7114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7114 = true := by
  decide +kernel

theorem tot7114 : totK PD2M8K2 D2M8K2.t7114 = [0, 0, 0, 321977856555, 456396667551, 72117522391, 1021600638, 0] := by
  decide +kernel

theorem rows7115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7115 = true := by
  decide +kernel

theorem tot7115 : totK PD2M8K2 D2M8K2.t7115 = [0, 0, 85071397234, 333799264450, 336554156555, 81801711618, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
