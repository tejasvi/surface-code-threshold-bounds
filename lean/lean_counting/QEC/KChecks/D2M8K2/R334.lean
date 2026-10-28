import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1336 = true := by
  decide +kernel

theorem tot1336 : totK PD2M8K2 D2M8K2.t1336 = [0, 192768216010, 485226261754, 201671843952, 6360151198, 0, 0, 0] := by
  decide +kernel

theorem rows1337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1337 = true := by
  decide +kernel

theorem tot1337 : totK PD2M8K2 D2M8K2.t1337 = [0, 0, 289023266312, 493818319895, 91645540201, 1310285577, 0, 0] := by
  decide +kernel

theorem rows1338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1338 = true := by
  decide +kernel

theorem tot1338 : totK PD2M8K2 D2M8K2.t1338 = [0, 92268877488, 387244914078, 383655083223, 42500611867, 0, 0, 0] := by
  decide +kernel

theorem rows1339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1339 = true := by
  decide +kernel

theorem tot1339 : totK PD2M8K2 D2M8K2.t1339 = [0, 171406050853, 443988027876, 258981814499, 20571423885, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
