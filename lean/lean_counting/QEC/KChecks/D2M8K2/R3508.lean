import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14032 = true := by
  decide +kernel

theorem tot14032 : totK PD2M8K2 D2M8K2.t14032 = [0, 0, 193074636352, 458764861799, 233352554105, 13459648627, 0, 0] := by
  decide +kernel

theorem rows14033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14033 = true := by
  decide +kernel

theorem tot14033 : totK PD2M8K2 D2M8K2.t14033 = [0, 55954175340, 216926470449, 414191515947, 193929694079, 8165763945, 0, 0] := by
  decide +kernel

theorem rows14034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14034 = true := by
  decide +kernel

theorem tot14034 : totK PD2M8K2 D2M8K2.t14034 = [0, 190191938275, 466079401886, 248847925985, 23144501495, 0, 0, 0] := by
  decide +kernel

theorem rows14035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14035 = true := by
  decide +kernel

theorem tot14035 : totK PD2M8K2 D2M8K2.t14035 = [0, 192429097505, 474227077404, 222607261513, 12490998278, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
