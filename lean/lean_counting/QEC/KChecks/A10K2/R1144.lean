import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4576 = true := by
  decide +kernel

theorem tot4576 : totK PA10K2 A10K2.t4576 = [0, 369723294981, 1706592805840, 2075173453333, 605248688902, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4577 = true := by
  decide +kernel

theorem tot4577 : totK PA10K2 A10K2.t4577 = [0, 0, 680704931943, 2155091854126, 1603154490445, 237829617416, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4578 = true := by
  decide +kernel

theorem tot4578 : totK PA10K2 A10K2.t4578 = [0, 554803763168, 1928205145908, 1934477911316, 536144331758, 47548777780, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4579 = true := by
  decide +kernel

theorem tot4579 : totK PA10K2 A10K2.t4579 = [0, 42649034548, 720382513472, 2140787054297, 1752348194655, 309352321743, 6962742351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
