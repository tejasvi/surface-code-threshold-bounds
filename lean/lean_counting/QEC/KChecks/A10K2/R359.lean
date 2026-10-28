import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1436 = true := by
  decide +kernel

theorem tot1436 : totK PA10K2 A10K2.t1436 = [0, 0, 0, 580138270545, 1863775222243, 1764594528858, 537102736986, 48424257799, 0, 0] := by
  decide +kernel

theorem rows1437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1437 = true := by
  decide +kernel

theorem tot1437 : totK PA10K2 A10K2.t1437 = [0, 0, 0, 252544515425, 1473507080370, 2190640510229, 798275358076, 60544467592, 0, 0] := by
  decide +kernel

theorem rows1438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1438 = true := by
  decide +kernel

theorem tot1438 : totK PA10K2 A10K2.t1438 = [0, 0, 0, 0, 506560630045, 1852913163655, 1758498718165, 471858129123, 30650496230, 0] := by
  decide +kernel

theorem rows1439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1439 = true := by
  decide +kernel

theorem tot1439 : totK PA10K2 A10K2.t1439 = [0, 0, 0, 464878800056, 1746836798380, 1886839769800, 547658958893, 48666249715, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
