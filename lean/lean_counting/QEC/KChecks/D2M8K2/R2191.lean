import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8764 = true := by
  decide +kernel

theorem tot8764 : totK PD2M8K2 D2M8K2.t8764 = [0, 0, 189283094351, 486278581170, 217060878971, 10992110171, 0, 0] := by
  decide +kernel

theorem rows8765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8765 = true := by
  decide +kernel

theorem tot8765 : totK PD2M8K2 D2M8K2.t8765 = [0, 0, 142769925197, 456483529754, 267959132803, 17498914433, 0, 0] := by
  decide +kernel

theorem rows8766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8766 = true := by
  decide +kernel

theorem tot8766 : totK PD2M8K2 D2M8K2.t8766 = [0, 0, 0, 338355447511, 475211468786, 58157092157, 0, 0] := by
  decide +kernel

theorem rows8767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8767 = true := by
  decide +kernel

theorem tot8767 : totK PD2M8K2 D2M8K2.t8767 = [0, 0, 183603346047, 400493796420, 256554868855, 50974222610, 1271866555, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
