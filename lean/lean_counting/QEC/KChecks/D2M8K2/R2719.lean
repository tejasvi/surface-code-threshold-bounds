import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10876 = true := by
  decide +kernel

theorem tot10876 : totK PD2M8K2 D2M8K2.t10876 = [0, 172848159982, 475460682933, 248895110967, 13782265251, 0, 0, 0] := by
  decide +kernel

theorem rows10877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10877 = true := by
  decide +kernel

theorem tot10877 : totK PD2M8K2 D2M8K2.t10877 = [0, 0, 288856653665, 501308235829, 112300026978, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10878 = true := by
  decide +kernel

theorem tot10878 : totK PD2M8K2 D2M8K2.t10878 = [0, 0, 195967285039, 476382683515, 194695964700, 12052611869, 0, 0] := by
  decide +kernel

theorem rows10879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10879 = true := by
  decide +kernel

theorem tot10879 : totK PD2M8K2 D2M8K2.t10879 = [0, 180188373297, 442026889181, 259288376760, 28199847990, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
