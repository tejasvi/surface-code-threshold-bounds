import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1168 = true := by
  decide +kernel

theorem tot1168 : totK PD2M8K2 D2M8K2.t1168 = [0, 0, 91428938205, 414465541519, 334841260640, 35729513135, 0, 0] := by
  decide +kernel

theorem rows1169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1169 = true := by
  decide +kernel

theorem tot1169 : totK PD2M8K2 D2M8K2.t1169 = [0, 0, 172506471528, 461336370608, 227248107422, 14293943931, 0, 0] := by
  decide +kernel

theorem rows1170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1170 = true := by
  decide +kernel

theorem tot1170 : totK PD2M8K2 D2M8K2.t1170 = [0, 0, 215598133461, 503197074033, 165312598705, 2954213869, 0, 0] := by
  decide +kernel

theorem rows1171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1171 = true := by
  decide +kernel

theorem tot1171 : totK PD2M8K2 D2M8K2.t1171 = [0, 0, 190376830859, 457580786732, 219271114429, 17982963062, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
