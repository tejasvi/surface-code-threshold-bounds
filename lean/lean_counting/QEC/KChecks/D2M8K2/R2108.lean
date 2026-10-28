import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8432 = true := by
  decide +kernel

theorem tot8432 : totK PD2M8K2 D2M8K2.t8432 = [0, 18872627066, 202220343523, 459274554824, 193118625173, 12451903996, 0, 0] := by
  decide +kernel

theorem rows8433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8433 = true := by
  decide +kernel

theorem tot8433 : totK PD2M8K2 D2M8K2.t8433 = [0, 211853225389, 472523760596, 192932131119, 9727964516, 0, 0, 0] := by
  decide +kernel

theorem rows8434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8434 = true := by
  decide +kernel

theorem tot8434 : totK PD2M8K2 D2M8K2.t8434 = [0, 189009670259, 470830118548, 221087439091, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows8435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8435 = true := by
  decide +kernel

theorem tot8435 : totK PD2M8K2 D2M8K2.t8435 = [0, 0, 283910995063, 488588197965, 106563604917, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
