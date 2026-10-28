import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12284 = true := by
  decide +kernel

theorem tot12284 : totK PD2M8K2 D2M8K2.t12284 = [188883436867, 462510086845, 252879480176, 23048968184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12285 = true := by
  decide +kernel

theorem tot12285 : totK PD2M8K2 D2M8K2.t12285 = [189563240406, 480228551246, 226700329727, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12286 = true := by
  decide +kernel

theorem tot12286 : totK PD2M8K2 D2M8K2.t12286 = [18591110785, 302650765669, 468659638689, 100666372276, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows12287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12287 = true := by
  decide +kernel

theorem tot12287 : totK PD2M8K2 D2M8K2.t12287 = [0, 204740531178, 475454596701, 190832531810, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
