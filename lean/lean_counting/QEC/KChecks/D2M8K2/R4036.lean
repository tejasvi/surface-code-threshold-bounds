import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16144 = true := by
  decide +kernel

theorem tot16144 : totK PD2M8K2 D2M8K2.t16144 = [0, 188150062161, 457762802668, 245412737394, 23050312993, 0, 0, 0] := by
  decide +kernel

theorem rows16145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16145 = true := by
  decide +kernel

theorem tot16145 : totK PD2M8K2 D2M8K2.t16145 = [0, 198734390863, 475122902544, 229276233533, 14326083334, 0, 0, 0] := by
  decide +kernel

theorem rows16146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16146 = true := by
  decide +kernel

theorem tot16146 : totK PD2M8K2 D2M8K2.t16146 = [0, 19689835847, 309891356050, 464228437765, 102160444714, 1268739303, 0, 0] := by
  decide +kernel

theorem rows16147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16147 = true := by
  decide +kernel

theorem tot16147 : totK PD2M8K2 D2M8K2.t16147 = [0, 0, 211681451254, 483591448923, 189103206542, 7439461435, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
