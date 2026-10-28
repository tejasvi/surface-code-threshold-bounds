import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t820 = true := by
  decide +kernel

theorem tot820 : totK PD2M8K2 D2M8K2.t820 = [0, 102956060767, 426195752496, 335445901423, 28635439933, 0, 0, 0] := by
  decide +kernel

theorem rows821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t821 = true := by
  decide +kernel

theorem tot821 : totK PD2M8K2 D2M8K2.t821 = [0, 0, 289437926652, 509844168242, 91255888324, 1096505104, 0, 0] := by
  decide +kernel

theorem rows822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t822 = true := by
  decide +kernel

theorem tot822 : totK PD2M8K2 D2M8K2.t822 = [0, 171260530109, 383008375799, 247887038325, 75910483223, 3884009855, 0, 0] := by
  decide +kernel

theorem rows823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t823 = true := by
  decide +kernel

theorem tot823 : totK PD2M8K2 D2M8K2.t823 = [0, 156240687809, 442550532405, 278292153808, 26226652666, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
