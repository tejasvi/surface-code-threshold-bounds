import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t992 = true := by
  decide +kernel

theorem tot992 : totK PD2M8K2 D2M8K2.t992 = [157241655014, 366315221657, 244434732269, 123326957940, 13555654450, 0, 0, 0] := by
  decide +kernel

theorem rows993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t993 = true := by
  decide +kernel

theorem tot993 : totK PD2M8K2 D2M8K2.t993 = [173877274957, 449854118276, 250170349472, 18193280786, 0, 0, 0, 0] := by
  decide +kernel

theorem rows994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t994 = true := by
  decide +kernel

theorem tot994 : totK PD2M8K2 D2M8K2.t994 = [78913304730, 341058728024, 378734166323, 83786091695, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t995 = true := by
  decide +kernel

theorem tot995 : totK PD2M8K2 D2M8K2.t995 = [12125792049, 323071297270, 505425012282, 69818059462, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
