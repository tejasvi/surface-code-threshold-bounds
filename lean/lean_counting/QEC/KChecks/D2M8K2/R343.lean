import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1372 = true := by
  decide +kernel

theorem tot1372 : totK PD2M8K2 D2M8K2.t1372 = [0, 0, 207391909351, 494151302421, 182639887868, 5342990109, 0, 0] := by
  decide +kernel

theorem rows1373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1373 = true := by
  decide +kernel

theorem tot1373 : totK PD2M8K2 D2M8K2.t1373 = [0, 0, 206031673196, 491971232674, 171757772520, 5106786593, 0, 0] := by
  decide +kernel

theorem rows1374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1374 = true := by
  decide +kernel

theorem tot1374 : totK PD2M8K2 D2M8K2.t1374 = [0, 0, 0, 300236505869, 455927029808, 88228918691, 1369150432, 0] := by
  decide +kernel

theorem rows1375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1375 = true := by
  decide +kernel

theorem tot1375 : totK PD2M8K2 D2M8K2.t1375 = [0, 0, 86929735316, 405813030626, 332160511030, 28838706053, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
