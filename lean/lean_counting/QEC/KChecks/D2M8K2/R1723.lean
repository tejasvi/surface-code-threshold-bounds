import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6892 = true := by
  decide +kernel

theorem tot6892 : totK PD2M8K2 D2M8K2.t6892 = [0, 117372596139, 409950402105, 319368889396, 39132080637, 0, 0, 0] := by
  decide +kernel

theorem rows6893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6893 = true := by
  decide +kernel

theorem tot6893 : totK PD2M8K2 D2M8K2.t6893 = [0, 165732653802, 434607817172, 268096138041, 27818717784, 0, 0, 0] := by
  decide +kernel

theorem rows6894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6894 = true := by
  decide +kernel

theorem tot6894 : totK PD2M8K2 D2M8K2.t6894 = [0, 117928812513, 412549124922, 323898026451, 31843014431, 0, 0, 0] := by
  decide +kernel

theorem rows6895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6895 = true := by
  decide +kernel

theorem tot6895 : totK PD2M8K2 D2M8K2.t6895 = [0, 0, 259804923531, 461996783089, 131687237203, 4931404646, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
