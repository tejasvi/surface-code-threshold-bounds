import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13128 = true := by
  decide +kernel

theorem tot13128 : totK PD2M8K2 D2M8K2.t13128 = [0, 70799043915, 335929174822, 409625775996, 89054378183, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13129 = true := by
  decide +kernel

theorem tot13129 : totK PD2M8K2 D2M8K2.t13129 = [0, 0, 219411360670, 490292327945, 172120930342, 9482920370, 0, 0] := by
  decide +kernel

theorem rows13130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13130 = true := by
  decide +kernel

theorem tot13130 : totK PD2M8K2 D2M8K2.t13130 = [0, 157133675824, 410729693018, 269025766483, 57116132526, 2569691499, 0, 0] := by
  decide +kernel

theorem rows13131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13131 = true := by
  decide +kernel

theorem tot13131 : totK PD2M8K2 D2M8K2.t13131 = [0, 171744648127, 438241384612, 269186704268, 30215549995, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
