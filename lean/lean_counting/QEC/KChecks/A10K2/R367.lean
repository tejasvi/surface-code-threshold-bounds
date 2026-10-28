import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1468 = true := by
  decide +kernel

theorem tot1468 : totK PA10K2 A10K2.t1468 = [0, 0, 0, 295090880714, 1214777451490, 1875011185303, 1091215381677, 180973809845, 6354482628, 0] := by
  decide +kernel

theorem rows1469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1469 = true := by
  decide +kernel

theorem tot1469 : totK PA10K2 A10K2.t1469 = [0, 0, 0, 290709251288, 1469234706932, 2207971721225, 912644327131, 81111660753, 0, 0] := by
  decide +kernel

theorem rows1470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1470 = true := by
  decide +kernel

theorem tot1470 : totK PA10K2 A10K2.t1470 = [0, 0, 0, 292156546580, 1362359750868, 1975138585126, 1113690042785, 218090183181, 6853348008, 0] := by
  decide +kernel

theorem rows1471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1471 = true := by
  decide +kernel

theorem tot1471 : totK PA10K2 A10K2.t1471 = [0, 0, 0, 513223753008, 1832900681325, 1876217676506, 475898853575, 22976955917, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
