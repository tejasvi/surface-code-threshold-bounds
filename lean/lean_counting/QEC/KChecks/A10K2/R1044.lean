import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4176 = true := by
  decide +kernel

theorem tot4176 : totK PA10K2 A10K2.t4176 = [482075982605, 1690177813037, 1902703858001, 733292628568, 78915738845, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4177 = true := by
  decide +kernel

theorem tot4177 : totK PA10K2 A10K2.t4177 = [297317356254, 1545608526829, 2126833024818, 817366883646, 60102351277, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4178 = true := by
  decide +kernel

theorem tot4178 : totK PA10K2 A10K2.t4178 = [0, 676657759747, 2184160861264, 1629405964802, 264008982269, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4179 = true := by
  decide +kernel

theorem tot4179 : totK PA10K2 A10K2.t4179 = [0, 458237146126, 1821372967285, 1980570713750, 564510095091, 32523532663, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
