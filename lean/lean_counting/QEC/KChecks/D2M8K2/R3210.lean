import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12840 = true := by
  decide +kernel

theorem tot12840 : totK PD2M8K2 D2M8K2.t12840 = [0, 172133514114, 442448074807, 278688002252, 30343566252, 0, 0, 0] := by
  decide +kernel

theorem rows12841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12841 = true := by
  decide +kernel

theorem tot12841 : totK PD2M8K2 D2M8K2.t12841 = [0, 125250872087, 456425187662, 295608406013, 23634285059, 0, 0, 0] := by
  decide +kernel

theorem rows12842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12842 = true := by
  decide +kernel

theorem tot12842 : totK PD2M8K2 D2M8K2.t12842 = [0, 0, 283790176393, 525372946170, 103481563911, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12843 = true := by
  decide +kernel

theorem tot12843 : totK PD2M8K2 D2M8K2.t12843 = [0, 0, 213978803666, 494507550538, 174219956882, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
