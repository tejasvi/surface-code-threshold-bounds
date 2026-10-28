import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13104 = true := by
  decide +kernel

theorem tot13104 : totK PD2M8K2 D2M8K2.t13104 = [0, 0, 37647871296, 302135321204, 420565872386, 149566529485, 9971490272, 0] := by
  decide +kernel

theorem rows13105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13105 = true := by
  decide +kernel

theorem tot13105 : totK PD2M8K2 D2M8K2.t13105 = [0, 0, 0, 230768470669, 488193754907, 170566501565, 5206224793, 0] := by
  decide +kernel

theorem rows13106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13106 = true := by
  decide +kernel

theorem tot13106 : totK PD2M8K2 D2M8K2.t13106 = [0, 0, 177507325160, 445150454817, 277116259545, 34720655825, 0, 0] := by
  decide +kernel

theorem rows13107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13107 = true := by
  decide +kernel

theorem tot13107 : totK PD2M8K2 D2M8K2.t13107 = [0, 0, 166849056618, 463361686925, 256772883862, 17492249845, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
