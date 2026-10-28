import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1000 = true := by
  decide +kernel

theorem tot1000 : totK PD2M8K2 D2M8K2.t1000 = [173329609152, 399541573777, 246373509076, 82502232011, 5551403096, 0, 0, 0] := by
  decide +kernel

theorem rows1001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1001 = true := by
  decide +kernel

theorem tot1001 : totK PD2M8K2 D2M8K2.t1001 = [177144735503, 434736105649, 275925009904, 29702468286, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1002 = true := by
  decide +kernel

theorem tot1002 : totK PD2M8K2 D2M8K2.t1002 = [83558568254, 406143867891, 353503910956, 47806929825, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows1003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1003 = true := by
  decide +kernel

theorem tot1003 : totK PD2M8K2 D2M8K2.t1003 = [0, 221654043214, 492192451427, 172944788756, 8470662040, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
