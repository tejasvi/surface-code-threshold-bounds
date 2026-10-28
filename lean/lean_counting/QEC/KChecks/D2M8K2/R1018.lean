import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4072 = true := by
  decide +kernel

theorem tot4072 : totK PD2M8K2 D2M8K2.t4072 = [0, 76987791727, 298416502530, 406126060953, 112643476164, 3884009855, 0, 0] := by
  decide +kernel

theorem rows4073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4073 = true := by
  decide +kernel

theorem tot4073 : totK PD2M8K2 D2M8K2.t4073 = [0, 177902928000, 464590192788, 255765862023, 23188875746, 0, 0, 0] := by
  decide +kernel

theorem rows4074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4074 = true := by
  decide +kernel

theorem tot4074 : totK PD2M8K2 D2M8K2.t4074 = [0, 161409159507, 468328023944, 270452379450, 16997923186, 0, 0, 0] := by
  decide +kernel

theorem rows4075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4075 = true := by
  decide +kernel

theorem tot4075 : totK PD2M8K2 D2M8K2.t4075 = [0, 0, 278994337202, 499502529676, 117680292885, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
