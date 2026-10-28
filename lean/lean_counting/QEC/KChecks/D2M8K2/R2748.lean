import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10992 = true := by
  decide +kernel

theorem tot10992 : totK PD2M8K2 D2M8K2.t10992 = [0, 207240035867, 490976930248, 179784276505, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows10993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10993 = true := by
  decide +kernel

theorem tot10993 : totK PD2M8K2 D2M8K2.t10993 = [0, 180045355203, 446603382222, 231533584586, 18444763256, 0, 0, 0] := by
  decide +kernel

theorem rows10994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10994 = true := by
  decide +kernel

theorem tot10994 : totK PD2M8K2 D2M8K2.t10994 = [0, 189718686160, 481080809011, 204461709184, 9653832318, 0, 0, 0] := by
  decide +kernel

theorem rows10995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10995 = true := by
  decide +kernel

theorem tot10995 : totK PD2M8K2 D2M8K2.t10995 = [0, 136712622874, 438557056684, 269237323703, 19982006368, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
