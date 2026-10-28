import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10556 = true := by
  decide +kernel

theorem tot10556 : totK PD2M8K2 D2M8K2.t10556 = [0, 0, 194985449694, 488965909771, 228249406345, 11427213771, 0, 0] := by
  decide +kernel

theorem rows10557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10557 = true := by
  decide +kernel

theorem tot10557 : totK PD2M8K2 D2M8K2.t10557 = [0, 0, 166082085129, 437029103833, 281788743308, 30187218494, 0, 0] := by
  decide +kernel

theorem rows10558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10558 = true := by
  decide +kernel

theorem tot10558 : totK PD2M8K2 D2M8K2.t10558 = [0, 0, 118073845999, 450659091176, 309055508056, 27116340772, 0, 0] := by
  decide +kernel

theorem rows10559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10559 = true := by
  decide +kernel

theorem tot10559 : totK PD2M8K2 D2M8K2.t10559 = [0, 0, 0, 238000450040, 511808913234, 135756620251, 4031931762, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
