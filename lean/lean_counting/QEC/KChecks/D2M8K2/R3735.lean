import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14940 = true := by
  decide +kernel

theorem tot14940 : totK PD2M8K2 D2M8K2.t14940 = [0, 0, 204893575846, 494111909265, 169519652678, 3630826045, 0, 0] := by
  decide +kernel

theorem rows14941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14941 = true := by
  decide +kernel

theorem tot14941 : totK PD2M8K2 D2M8K2.t14941 = [0, 0, 170562324654, 468952717756, 228379277500, 10816184264, 0, 0] := by
  decide +kernel

theorem rows14942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14942 = true := by
  decide +kernel

theorem tot14942 : totK PD2M8K2 D2M8K2.t14942 = [0, 20021956556, 176331326710, 449753823470, 236595203466, 17376665387, 0, 0] := by
  decide +kernel

theorem rows14943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14943 = true := by
  decide +kernel

theorem tot14943 : totK PD2M8K2 D2M8K2.t14943 = [0, 162581909437, 449369220809, 282003632429, 29995732368, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
