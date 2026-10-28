import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15768 = true := by
  decide +kernel

theorem tot15768 : totK PD2M8K2 D2M8K2.t15768 = [0, 0, 0, 214945096118, 488833178120, 200812683469, 12064694307, 0] := by
  decide +kernel

theorem rows15769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15769 = true := by
  decide +kernel

theorem tot15769 : totK PD2M8K2 D2M8K2.t15769 = [0, 0, 104100811831, 360768755314, 338160557603, 100912131578, 4246544562, 0] := by
  decide +kernel

theorem rows15770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15770 = true := by
  decide +kernel

theorem tot15770 : totK PD2M8K2 D2M8K2.t15770 = [0, 0, 159220814462, 439202010882, 276586357908, 29604968028, 0, 0] := by
  decide +kernel

theorem rows15771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15771 = true := by
  decide +kernel

theorem tot15771 : totK PD2M8K2 D2M8K2.t15771 = [0, 0, 155293964091, 449502941021, 272625319835, 23381885958, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
