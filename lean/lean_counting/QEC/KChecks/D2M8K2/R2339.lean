import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9356 = true := by
  decide +kernel

theorem tot9356 : totK PD2M8K2 D2M8K2.t9356 = [0, 71446184384, 254462599893, 383682153347, 173656923213, 8104085798, 0, 0] := by
  decide +kernel

theorem rows9357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9357 = true := by
  decide +kernel

theorem tot9357 : totK PD2M8K2 D2M8K2.t9357 = [0, 163008752683, 436702889535, 279745582261, 30484327524, 0, 0, 0] := by
  decide +kernel

theorem rows9358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9358 = true := by
  decide +kernel

theorem tot9358 : totK PD2M8K2 D2M8K2.t9358 = [0, 149029353690, 447832560423, 284163706644, 23183373708, 0, 0, 0] := by
  decide +kernel

theorem rows9359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9359 = true := by
  decide +kernel

theorem tot9359 : totK PD2M8K2 D2M8K2.t9359 = [0, 0, 258452805993, 486058129184, 144519943126, 8417083954, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
