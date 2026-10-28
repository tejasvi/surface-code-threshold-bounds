import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1392 = true := by
  decide +kernel

theorem tot1392 : totK PA10K2 A10K2.t1392 = [0, 0, 0, 476443728743, 1789290080518, 2074554348692, 749517894665, 54536254033, 0, 0] := by
  decide +kernel

theorem rows1393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1393 = true := by
  decide +kernel

theorem tot1393 : totK PA10K2 A10K2.t1393 = [0, 0, 0, 616719774236, 2095822800484, 1881997703361, 468680885103, 29840961845, 0, 0] := by
  decide +kernel

theorem rows1394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1394 = true := by
  decide +kernel

theorem tot1394 : totK PA10K2 A10K2.t1394 = [0, 0, 0, 201165398740, 1182478737978, 2075349399722, 1230537310629, 187942277487, 6066958478, 0] := by
  decide +kernel

theorem rows1395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1395 = true := by
  decide +kernel

theorem tot1395 : totK PA10K2 A10K2.t1395 = [0, 0, 0, 212650738990, 1054983229426, 1859814294866, 1421164877796, 373531318135, 28503589898, 0] := by
  decide +kernel

end QECKChecks.A10K2
