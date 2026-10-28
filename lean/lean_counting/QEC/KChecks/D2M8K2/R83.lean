import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t332 = true := by
  decide +kernel

theorem tot332 : totK PD2M8K2 D2M8K2.t332 = [0, 162396262016, 451284747436, 283515594983, 28496840222, 0, 0, 0] := by
  decide +kernel

theorem rows333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t333 = true := by
  decide +kernel

theorem tot333 : totK PD2M8K2 D2M8K2.t333 = [0, 210227875400, 483058656623, 207587205664, 8852302962, 0, 0, 0] := by
  decide +kernel

theorem rows334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t334 = true := by
  decide +kernel

theorem tot334 : totK PD2M8K2 D2M8K2.t334 = [0, 36725488451, 274732547532, 399908215122, 179636972625, 21385604922, 0, 0] := by
  decide +kernel

theorem rows335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t335 = true := by
  decide +kernel

theorem tot335 : totK PD2M8K2 D2M8K2.t335 = [0, 0, 212275248207, 472059998260, 193278198232, 7658844075, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
