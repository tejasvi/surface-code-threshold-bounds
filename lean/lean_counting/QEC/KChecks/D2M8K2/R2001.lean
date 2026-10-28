import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8004 = true := by
  decide +kernel

theorem tot8004 : totK PD2M8K2 D2M8K2.t8004 = [0, 0, 207204175136, 481153010016, 194868057576, 9785417543, 0, 0] := by
  decide +kernel

theorem rows8005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8005 = true := by
  decide +kernel

theorem tot8005 : totK PD2M8K2 D2M8K2.t8005 = [0, 0, 186994593081, 473852789211, 208382401522, 12534051746, 0, 0] := by
  decide +kernel

theorem rows8006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8006 = true := by
  decide +kernel

theorem tot8006 : totK PD2M8K2 D2M8K2.t8006 = [0, 0, 0, 319070614084, 480206144582, 65851739964, 1310517177, 0] := by
  decide +kernel

theorem rows8007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8007 = true := by
  decide +kernel

theorem tot8007 : totK PD2M8K2 D2M8K2.t8007 = [0, 0, 128999756440, 420807095915, 335437658857, 34873396498, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
