import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11676 = true := by
  decide +kernel

theorem tot11676 : totK PD2M8K2 D2M8K2.t11676 = [160348302782, 459814136872, 258924428247, 20358382612, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11677 = true := by
  decide +kernel

theorem tot11677 : totK PD2M8K2 D2M8K2.t11677 = [0, 244134621206, 509485104590, 135404711157, 2309606161, 0, 0, 0] := by
  decide +kernel

theorem rows11678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11678 = true := by
  decide +kernel

theorem tot11678 : totK PD2M8K2 D2M8K2.t11678 = [67923955290, 255606115622, 391101788220, 154103713494, 10740121073, 0, 0, 0] := by
  decide +kernel

theorem rows11679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11679 = true := by
  decide +kernel

theorem tot11679 : totK PD2M8K2 D2M8K2.t11679 = [187016165613, 463318934331, 250037978770, 23076592272, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
