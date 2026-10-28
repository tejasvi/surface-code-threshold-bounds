import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4372 = true := by
  decide +kernel

theorem tot4372 : totK PD2M8K2 D2M8K2.t4372 = [0, 86871980442, 343592034421, 388094475244, 81153684054, 1164319620, 0, 0] := by
  decide +kernel

theorem rows4373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4373 = true := by
  decide +kernel

theorem tot4373 : totK PD2M8K2 D2M8K2.t4373 = [0, 0, 210227058760, 488609133179, 169543001697, 9404247146, 0, 0] := by
  decide +kernel

theorem rows4374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4374 = true := by
  decide +kernel

theorem tot4374 : totK PD2M8K2 D2M8K2.t4374 = [0, 153659183205, 429948241172, 269402627860, 45296389492, 2481160468, 0, 0] := by
  decide +kernel

theorem rows4375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4375 = true := by
  decide +kernel

theorem tot4375 : totK PD2M8K2 D2M8K2.t4375 = [0, 154001878073, 431397820579, 274336894808, 31817671588, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
