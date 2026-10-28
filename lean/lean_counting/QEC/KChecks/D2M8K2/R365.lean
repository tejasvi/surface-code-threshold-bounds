import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1460 = true := by
  decide +kernel

theorem tot1460 : totK PD2M8K2 D2M8K2.t1460 = [0, 0, 0, 304754839619, 470270335556, 82469028269, 1135526696, 0] := by
  decide +kernel

theorem rows1461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1461 = true := by
  decide +kernel

theorem tot1461 : totK PD2M8K2 D2M8K2.t1461 = [0, 0, 80838430914, 322941203500, 351885291429, 93605040122, 4028038878, 0] := by
  decide +kernel

theorem rows1462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1462 = true := by
  decide +kernel

theorem tot1462 : totK PD2M8K2 D2M8K2.t1462 = [0, 0, 248562839887, 490911605697, 139881276037, 3836120568, 0, 0] := by
  decide +kernel

theorem rows1463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1463 = true := by
  decide +kernel

theorem tot1463 : totK PD2M8K2 D2M8K2.t1463 = [0, 0, 195334744845, 475302839164, 201603000626, 11428133182, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
