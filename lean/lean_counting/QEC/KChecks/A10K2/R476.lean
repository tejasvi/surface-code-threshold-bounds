import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1904 = true := by
  decide +kernel

theorem tot1904 : totK PA10K2 A10K2.t1904 = [0, 0, 547363148379, 1739905853752, 1835477289426, 690712735215, 65527055973, 0, 0, 0] := by
  decide +kernel

theorem rows1905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1905 = true := by
  decide +kernel

theorem tot1905 : totK PA10K2 A10K2.t1905 = [0, 0, 0, 973338072771, 2353980407760, 1227523078195, 119558514626, 0, 0, 0] := by
  decide +kernel

theorem rows1906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1906 = true := by
  decide +kernel

theorem tot1906 : totK PA10K2 A10K2.t1906 = [0, 0, 505809520447, 1798394947228, 1924249890285, 688003149676, 109294043602, 6121173289, 0, 0] := by
  decide +kernel

theorem rows1907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1907 = true := by
  decide +kernel

theorem tot1907 : totK PA10K2 A10K2.t1907 = [0, 285766734819, 1072122658596, 1649487029938, 1448071487228, 557464022649, 50499610055, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
