import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15280 = true := by
  decide +kernel

theorem tot15280 : totK PD2M8K2 D2M8K2.t15280 = [0, 0, 4294967296, 327858297297, 514208432686, 60962862340, 0, 0] := by
  decide +kernel

theorem rows15281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15281 = true := by
  decide +kernel

theorem tot15281 : totK PD2M8K2 D2M8K2.t15281 = [0, 0, 169759587928, 449776652712, 277429720502, 28976936317, 0, 0] := by
  decide +kernel

theorem rows15282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15282 = true := by
  decide +kernel

theorem tot15282 : totK PD2M8K2 D2M8K2.t15282 = [0, 0, 153154340858, 463394860291, 285827212903, 23859882800, 0, 0] := by
  decide +kernel

theorem rows15283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15283 = true := by
  decide +kernel

theorem tot15283 : totK PD2M8K2 D2M8K2.t15283 = [0, 0, 50849869571, 317531488960, 446060867967, 98382066214, 1535615586, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
