import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5352 = true := by
  decide +kernel

theorem tot5352 : totK PD2M8K2 D2M8K2.t5352 = [0, 180222879704, 459026320063, 256619210944, 22862353543, 0, 0, 0] := by
  decide +kernel

theorem rows5353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5353 = true := by
  decide +kernel

theorem tot5353 : totK PD2M8K2 D2M8K2.t5353 = [0, 155891747028, 461378125741, 266497588233, 16632024298, 0, 0, 0] := by
  decide +kernel

theorem rows5354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5354 = true := by
  decide +kernel

theorem tot5354 : totK PD2M8K2 D2M8K2.t5354 = [0, 0, 261211106542, 514037407057, 115305706959, 1164319620, 0, 0] := by
  decide +kernel

theorem rows5355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5355 = true := by
  decide +kernel

theorem tot5355 : totK PD2M8K2 D2M8K2.t5355 = [0, 64609315486, 240043423919, 390758593627, 167723219523, 10463041093, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
