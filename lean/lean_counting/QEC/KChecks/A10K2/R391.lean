import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1564 = true := by
  decide +kernel

theorem tot1564 : totK PA10K2 A10K2.t1564 = [0, 0, 293418347279, 1377989816636, 2151793121523, 1150115637931, 114726205802, 0, 0, 0] := by
  decide +kernel

theorem rows1565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1565 = true := by
  decide +kernel

theorem tot1565 : totK PA10K2 A10K2.t1565 = [0, 0, 0, 581589450439, 1964797677419, 1971610539855, 542433814402, 35031173917, 0, 0] := by
  decide +kernel

theorem rows1566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1566 = true := by
  decide +kernel

theorem tot1566 : totK PA10K2 A10K2.t1566 = [0, 0, 0, 469321903049, 1783074987078, 1881422365522, 499000943516, 31222411477, 0, 0] := by
  decide +kernel

theorem rows1567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1567 = true := by
  decide +kernel

theorem tot1567 : totK PA10K2 A10K2.t1567 = [0, 0, 0, 180321904391, 1164566463691, 2009979626882, 1169848954888, 253510806896, 20060612110, 0] := by
  decide +kernel

end QECKChecks.A10K2
