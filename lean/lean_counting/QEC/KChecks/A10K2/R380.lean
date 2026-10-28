import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1520 = true := by
  decide +kernel

theorem tot1520 : totK PA10K2 A10K2.t1520 = [0, 0, 482117243921, 1869828793392, 1890652338771, 485037423643, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows1521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1521 = true := by
  decide +kernel

theorem tot1521 : totK PA10K2 A10K2.t1521 = [0, 456550563288, 1670798987147, 1881649958009, 703210175369, 78752523016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1522 = true := by
  decide +kernel

theorem tot1522 : totK PA10K2 A10K2.t1522 = [0, 285599711294, 1458495791081, 2084429983804, 817390850091, 51330830718, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1523 = true := by
  decide +kernel

theorem tot1523 : totK PA10K2 A10K2.t1523 = [0, 297783531355, 1138964909880, 1769931893375, 1200452383198, 235349129180, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
