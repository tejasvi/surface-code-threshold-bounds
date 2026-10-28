import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5128 = true := by
  decide +kernel

theorem tot5128 : totK PD2M8K2 D2M8K2.t5128 = [0, 0, 155785623112, 406235115676, 281331298966, 64688726728, 2266161007, 0] := by
  decide +kernel

theorem rows5129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5129 = true := by
  decide +kernel

theorem tot5129 : totK PD2M8K2 D2M8K2.t5129 = [0, 0, 177606368184, 431788188070, 274070474539, 30587065052, 0, 0] := by
  decide +kernel

theorem rows5130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5130 = true := by
  decide +kernel

theorem tot5130 : totK PD2M8K2 D2M8K2.t5130 = [0, 0, 80460339412, 416478337598, 376056164719, 39055205614, 0, 0] := by
  decide +kernel

theorem rows5131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5131 = true := by
  decide +kernel

theorem tot5131 : totK PD2M8K2 D2M8K2.t5131 = [0, 0, 0, 212484333306, 492445559158, 171351183818, 6860571838, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
