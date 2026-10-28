import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8792 = true := by
  decide +kernel

theorem tot8792 : totK PD2M8K2 D2M8K2.t8792 = [0, 0, 206726516066, 475270473029, 205462114800, 9357067284, 0, 0] := by
  decide +kernel

theorem rows8793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8793 = true := by
  decide +kernel

theorem tot8793 : totK PD2M8K2 D2M8K2.t8793 = [0, 0, 177523976977, 475849711775, 233564156390, 12203296208, 0, 0] := by
  decide +kernel

theorem rows8794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8794 = true := by
  decide +kernel

theorem tot8794 : totK PD2M8K2 D2M8K2.t8794 = [0, 0, 188048814058, 461038819747, 225119547740, 12516610404, 0, 0] := by
  decide +kernel

theorem rows8795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8795 = true := by
  decide +kernel

theorem tot8795 : totK PD2M8K2 D2M8K2.t8795 = [0, 0, 201302264862, 486195793408, 211979292599, 11066126582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
