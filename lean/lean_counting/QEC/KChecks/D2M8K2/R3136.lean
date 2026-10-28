import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12544 = true := by
  decide +kernel

theorem tot12544 : totK PD2M8K2 D2M8K2.t12544 = [0, 0, 225144695593, 487537817203, 168600034758, 9482920370, 0, 0] := by
  decide +kernel

theorem rows12545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12545 = true := by
  decide +kernel

theorem tot12545 : totK PD2M8K2 D2M8K2.t12545 = [0, 153876230903, 406950026261, 273563129211, 56722261793, 2569691499, 0, 0] := by
  decide +kernel

theorem rows12546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12546 = true := by
  decide +kernel

theorem tot12546 : totK PD2M8K2 D2M8K2.t12546 = [0, 167489250347, 430023720569, 275409630415, 29485939160, 0, 0, 0] := by
  decide +kernel

theorem rows12547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12547 = true := by
  decide +kernel

theorem tot12547 : totK PD2M8K2 D2M8K2.t12547 = [0, 90854154917, 377120892256, 351298702126, 59685576852, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
