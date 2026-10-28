import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9516 = true := by
  decide +kernel

theorem tot9516 : totK PD2M8K2 D2M8K2.t9516 = [88453318852, 335500207491, 365017437925, 117029135124, 13135812311, 0, 0, 0] := by
  decide +kernel

theorem rows9517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9517 = true := by
  decide +kernel

theorem tot9517 : totK PD2M8K2 D2M8K2.t9517 = [0, 176384551713, 459641193496, 252191063906, 16215124949, 0, 0, 0] := by
  decide +kernel

theorem rows9518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9518 = true := by
  decide +kernel

theorem tot9518 : totK PD2M8K2 D2M8K2.t9518 = [72933215321, 244067242195, 390251208645, 182111830743, 8209931632, 0, 0, 0] := by
  decide +kernel

theorem rows9519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9519 = true := by
  decide +kernel

theorem tot9519 : totK PD2M8K2 D2M8K2.t9519 = [184259204858, 461400593157, 250752134480, 22969944954, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
