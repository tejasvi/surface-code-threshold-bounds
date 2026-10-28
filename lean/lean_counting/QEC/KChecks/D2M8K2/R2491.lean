import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9964 = true := by
  decide +kernel

theorem tot9964 : totK PD2M8K2 D2M8K2.t9964 = [0, 0, 65955660328, 356553484248, 428380906242, 41142113764, 0, 0] := by
  decide +kernel

theorem rows9965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9965 = true := by
  decide +kernel

theorem tot9965 : totK PD2M8K2 D2M8K2.t9965 = [0, 0, 176307545471, 479065427343, 248124265405, 14668645436, 0, 0] := by
  decide +kernel

theorem rows9966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9966 = true := by
  decide +kernel

theorem tot9966 : totK PD2M8K2 D2M8K2.t9966 = [0, 0, 217487889104, 463322010834, 217761131853, 17669886314, 0, 0] := by
  decide +kernel

theorem rows9967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9967 = true := by
  decide +kernel

theorem tot9967 : totK PD2M8K2 D2M8K2.t9967 = [0, 0, 189606952016, 475140161767, 209401582313, 7327878398, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
