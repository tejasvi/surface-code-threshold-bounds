import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5396 = true := by
  decide +kernel

theorem tot5396 : totK PA10K2 A10K2.t5396 = [0, 0, 551357255719, 1823944928068, 1827401287363, 504952506801, 31607162994, 0, 0, 0] := by
  decide +kernel

theorem rows5397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5397 = true := by
  decide +kernel

theorem tot5397 : totK PA10K2 A10K2.t5397 = [0, 0, 340083391325, 1603179474109, 2033164107260, 630461547296, 51402059204, 0, 0, 0] := by
  decide +kernel

theorem rows5398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5398 = true := by
  decide +kernel

theorem tot5398 : totK PA10K2 A10K2.t5398 = [0, 81682624723, 176679472003, 785849804596, 1989856723212, 1325696606535, 239904770714, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5399 = true := by
  decide +kernel

theorem tot5399 : totK PA10K2 A10K2.t5399 = [0, 366351634088, 1505005867118, 2110349330765, 1044390884087, 109696929541, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
