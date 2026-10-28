import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14168 = true := by
  decide +kernel

theorem tot14168 : totK PD2M8K2 D2M8K2.t14168 = [196516837485, 470144072261, 248036959206, 23350948179, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14169 = true := by
  decide +kernel

theorem tot14169 : totK PD2M8K2 D2M8K2.t14169 = [173035511169, 466305336619, 255501766948, 16535239914, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14170 = true := by
  decide +kernel

theorem tot14170 : totK PD2M8K2 D2M8K2.t14170 = [0, 292198702075, 498146808340, 116698018354, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows14171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14171 = true := by
  decide +kernel

theorem tot14171 : totK PD2M8K2 D2M8K2.t14171 = [0, 191078077099, 484116449954, 199533440736, 8634597626, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
