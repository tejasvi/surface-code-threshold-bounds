import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5096 = true := by
  decide +kernel

theorem tot5096 : totK PD2M8K2 D2M8K2.t5096 = [0, 0, 158422053002, 474720900535, 264233181935, 14961030598, 0, 0] := by
  decide +kernel

theorem rows5097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5097 = true := by
  decide +kernel

theorem tot5097 : totK PD2M8K2 D2M8K2.t5097 = [0, 0, 206258899052, 472504546273, 202603029753, 11051716772, 0, 0] := by
  decide +kernel

theorem rows5098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5098 = true := by
  decide +kernel

theorem tot5098 : totK PD2M8K2 D2M8K2.t5098 = [0, 0, 183909639383, 467746787513, 227078473055, 12370590376, 0, 0] := by
  decide +kernel

theorem rows5099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5099 = true := by
  decide +kernel

theorem tot5099 : totK PD2M8K2 D2M8K2.t5099 = [0, 0, 195388236388, 479368395966, 195065560043, 9170465948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
