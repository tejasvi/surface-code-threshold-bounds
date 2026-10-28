import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8204 = true := by
  decide +kernel

theorem tot8204 : totK PD2M8K2 D2M8K2.t8204 = [0, 0, 152809994679, 474160733161, 256430081690, 11894313774, 0, 0] := by
  decide +kernel

theorem rows8205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8205 = true := by
  decide +kernel

theorem tot8205 : totK PD2M8K2 D2M8K2.t8205 = [0, 0, 193884470982, 461625604241, 234569555144, 16220436538, 0, 0] := by
  decide +kernel

theorem rows8206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8206 = true := by
  decide +kernel

theorem tot8206 : totK PD2M8K2 D2M8K2.t8206 = [0, 0, 163631161496, 440332959621, 276567976321, 27927658571, 0, 0] := by
  decide +kernel

theorem rows8207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8207 = true := by
  decide +kernel

theorem tot8207 : totK PD2M8K2 D2M8K2.t8207 = [0, 0, 153138263010, 453810269698, 274645461060, 19992421626, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
