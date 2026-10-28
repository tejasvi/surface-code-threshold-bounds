import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4548 = true := by
  decide +kernel

theorem tot4548 : totK PD2M8K2 D2M8K2.t4548 = [0, 0, 52741071690, 357189459381, 441836873602, 41199487241, 0, 0] := by
  decide +kernel

theorem rows4549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4549 = true := by
  decide +kernel

theorem tot4549 : totK PD2M8K2 D2M8K2.t4549 = [0, 0, 189221033640, 483816031964, 229608114900, 13406725249, 0, 0] := by
  decide +kernel

theorem rows4550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4550 = true := by
  decide +kernel

theorem tot4550 : totK PD2M8K2 D2M8K2.t4550 = [0, 0, 198268752005, 459049280616, 242623364776, 18837324716, 0, 0] := by
  decide +kernel

theorem rows4551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4551 = true := by
  decide +kernel

theorem tot4551 : totK PD2M8K2 D2M8K2.t4551 = [0, 0, 172092715493, 449530762410, 281040865451, 29350723805, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
