import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11584 = true := by
  decide +kernel

theorem tot11584 : totK PD2M8K2 D2M8K2.t11584 = [0, 190381297397, 465497266041, 225010964210, 14867380226, 0, 0, 0] := by
  decide +kernel

theorem rows11585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11585 = true := by
  decide +kernel

theorem tot11585 : totK PD2M8K2 D2M8K2.t11585 = [0, 205745945233, 464872168959, 200688489442, 12595094539, 0, 0, 0] := by
  decide +kernel

theorem rows11586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11586 = true := by
  decide +kernel

theorem tot11586 : totK PD2M8K2 D2M8K2.t11586 = [0, 169803840572, 486146754334, 226887564855, 8671967938, 0, 0, 0] := by
  decide +kernel

theorem rows11587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11587 = true := by
  decide +kernel

theorem tot11587 : totK PD2M8K2 D2M8K2.t11587 = [0, 172657661581, 454774277701, 232996298149, 14858663033, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
