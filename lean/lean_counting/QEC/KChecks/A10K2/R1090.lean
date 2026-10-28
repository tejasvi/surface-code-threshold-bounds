import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4360 = true := by
  decide +kernel

theorem tot4360 : totK PA10K2 A10K2.t4360 = [0, 249468953483, 1374469057547, 2151684896648, 907272645537, 71955349285, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4361 = true := by
  decide +kernel

theorem tot4361 : totK PA10K2 A10K2.t4361 = [0, 0, 490987709367, 1857644391777, 1883166568032, 485037423643, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows4362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4362 = true := by
  decide +kernel

theorem tot4362 : totK PA10K2 A10K2.t4362 = [0, 475977597359, 1693005429074, 1840185871775, 678082097562, 74514475390, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4363 = true := by
  decide +kernel

theorem tot4363 : totK PA10K2 A10K2.t4363 = [0, 293434943870, 1491034580915, 2106015061236, 823565983895, 51330830718, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
