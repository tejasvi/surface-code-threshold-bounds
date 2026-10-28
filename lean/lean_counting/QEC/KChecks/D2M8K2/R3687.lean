import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14748 = true := by
  decide +kernel

theorem tot14748 : totK PD2M8K2 D2M8K2.t14748 = [0, 247105662283, 499000973196, 148067315421, 2304167554, 0, 0, 0] := by
  decide +kernel

theorem rows14749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14749 = true := by
  decide +kernel

theorem tot14749 : totK PD2M8K2 D2M8K2.t14749 = [0, 178611760604, 477524460198, 216257857664, 10135863696, 0, 0, 0] := by
  decide +kernel

theorem rows14750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14750 = true := by
  decide +kernel

theorem tot14750 : totK PD2M8K2 D2M8K2.t14750 = [0, 178586387761, 459345689719, 228834830013, 19219661456, 0, 0, 0] := by
  decide +kernel

theorem rows14751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14751 = true := by
  decide +kernel

theorem tot14751 : totK PD2M8K2 D2M8K2.t14751 = [0, 188902613544, 463037397492, 204427745301, 12206147664, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
