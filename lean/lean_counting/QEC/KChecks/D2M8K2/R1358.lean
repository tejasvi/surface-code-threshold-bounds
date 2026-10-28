import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5432 = true := by
  decide +kernel

theorem tot5432 : totK PD2M8K2 D2M8K2.t5432 = [0, 0, 0, 292387530193, 487342535018, 118253907386, 1260410359, 0] := by
  decide +kernel

theorem rows5433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5433 = true := by
  decide +kernel

theorem tot5433 : totK PD2M8K2 D2M8K2.t5433 = [0, 0, 0, 229453001699, 460360954448, 214937198651, 12887230512, 0] := by
  decide +kernel

theorem rows5434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5434 = true := by
  decide +kernel

theorem tot5434 : totK PD2M8K2 D2M8K2.t5434 = [0, 0, 0, 214933729989, 481766918390, 184868366047, 8467741327, 0] := by
  decide +kernel

theorem rows5435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5435 = true := by
  decide +kernel

theorem tot5435 : totK PD2M8K2 D2M8K2.t5435 = [0, 0, 0, 181061778664, 463472238181, 234383310094, 17011553985, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
