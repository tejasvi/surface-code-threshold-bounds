import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5452 = true := by
  decide +kernel

theorem tot5452 : totK PA10K2 A10K2.t5452 = [0, 0, 465515810549, 1802053707802, 1923019217320, 541662135180, 32021558464, 0, 0, 0] := by
  decide +kernel

theorem rows5453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5453 = true := by
  decide +kernel

theorem tot5453 : totK PA10K2 A10K2.t5453 = [0, 0, 290808337413, 1550694994791, 2195830993142, 747817428324, 45183675077, 0, 0, 0] := by
  decide +kernel

theorem rows5454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5454 = true := by
  decide +kernel

theorem tot5454 : totK PA10K2 A10K2.t5454 = [0, 0, 110302630917, 726307841359, 1785826585801, 1547088444473, 406305873334, 30650496230, 0, 0] := by
  decide +kernel

theorem rows5455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5455 = true := by
  decide +kernel

theorem tot5455 : totK PA10K2 A10K2.t5455 = [0, 0, 557190328990, 1904154362338, 1861787553171, 478377870010, 31608797364, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
