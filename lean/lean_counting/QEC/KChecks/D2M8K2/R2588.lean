import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10352 = true := by
  decide +kernel

theorem tot10352 : totK PD2M8K2 D2M8K2.t10352 = [0, 0, 181091003179, 474059521098, 221725039325, 11168585372, 0, 0] := by
  decide +kernel

theorem rows10353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10353 = true := by
  decide +kernel

theorem tot10353 : totK PD2M8K2 D2M8K2.t10353 = [0, 0, 198716072758, 486540824343, 194681920092, 9598064859, 0, 0] := by
  decide +kernel

theorem rows10354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10354 = true := by
  decide +kernel

theorem tot10354 : totK PD2M8K2 D2M8K2.t10354 = [0, 0, 207670934380, 489121574932, 179723969607, 5098257138, 0, 0] := by
  decide +kernel

theorem rows10355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10355 = true := by
  decide +kernel

theorem tot10355 : totK PD2M8K2 D2M8K2.t10355 = [0, 0, 0, 290031129311, 499115286415, 81169333641, 1310285577, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
