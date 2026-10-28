import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16308 = true := by
  decide +kernel

theorem tot16308 : totK PD2M8K2 D2M8K2.t16308 = [0, 0, 0, 206361461634, 495117359556, 187316785069, 6714578472, 0] := by
  decide +kernel

theorem rows16309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16309 = true := by
  decide +kernel

theorem tot16309 : totK PD2M8K2 D2M8K2.t16309 = [0, 0, 0, 187426300610, 458423897876, 224033258869, 16639888180, 0] := by
  decide +kernel

theorem rows16310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16310 = true := by
  decide +kernel

theorem tot16310 : totK PD2M8K2 D2M8K2.t16310 = [0, 0, 0, 87965506125, 377863219132, 323852471973, 51586225958, 1128585284] := by
  decide +kernel

theorem rows16311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16311 = true := by
  decide +kernel

theorem tot16311 : totK PD2M8K2 D2M8K2.t16311 = [0, 0, 0, 0, 294314092508, 445906952832, 106397017105, 4006170569] := by
  decide +kernel

end QECKChecks.D2M8K2
