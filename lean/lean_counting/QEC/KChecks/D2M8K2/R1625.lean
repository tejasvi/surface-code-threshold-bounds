import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6500 = true := by
  decide +kernel

theorem tot6500 : totK PD2M8K2 D2M8K2.t6500 = [0, 184415615032, 477027168650, 229129012825, 12423391470, 0, 0, 0] := by
  decide +kernel

theorem rows6501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6501 = true := by
  decide +kernel

theorem tot6501 : totK PD2M8K2 D2M8K2.t6501 = [0, 0, 285941069164, 478675075414, 122976825065, 2926763925, 0, 0] := by
  decide +kernel

theorem rows6502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6502 = true := by
  decide +kernel

theorem tot6502 : totK PD2M8K2 D2M8K2.t6502 = [0, 69347112629, 322620730464, 388560810757, 89950048840, 1186940923, 0, 0] := by
  decide +kernel

theorem rows6503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6503 = true := by
  decide +kernel

theorem tot6503 : totK PD2M8K2 D2M8K2.t6503 = [0, 175995412770, 440034317734, 273612569703, 30316101566, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
