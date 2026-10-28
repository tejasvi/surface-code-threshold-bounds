import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7876 = true := by
  decide +kernel

theorem tot7876 : totK PD2M8K2 D2M8K2.t7876 = [0, 0, 199879938167, 482962869146, 210659603021, 11056080877, 0, 0] := by
  decide +kernel

theorem rows7877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7877 = true := by
  decide +kernel

theorem tot7877 : totK PD2M8K2 D2M8K2.t7877 = [0, 0, 202779333371, 468253138208, 205462228474, 12064174497, 0, 0] := by
  decide +kernel

theorem rows7878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7878 = true := by
  decide +kernel

theorem tot7878 : totK PD2M8K2 D2M8K2.t7878 = [0, 0, 11526003605, 330933949317, 442918283509, 71032100857, 1021600638, 0] := by
  decide +kernel

theorem rows7879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7879 = true := by
  decide +kernel

theorem tot7879 : totK PD2M8K2 D2M8K2.t7879 = [0, 0, 80882125628, 322670613666, 356097877038, 82887133152, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
