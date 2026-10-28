import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11352 = true := by
  decide +kernel

theorem tot11352 : totK PD2M8K2 D2M8K2.t11352 = [0, 179921898013, 470275529000, 241906526237, 13683499228, 0, 0, 0] := by
  decide +kernel

theorem rows11353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11353 = true := by
  decide +kernel

theorem tot11353 : totK PD2M8K2 D2M8K2.t11353 = [0, 193520705473, 476566867426, 221540247120, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows11354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11354 = true := by
  decide +kernel

theorem tot11354 : totK PD2M8K2 D2M8K2.t11354 = [0, 211411119644, 494533750824, 186077230436, 5064232198, 0, 0, 0] := by
  decide +kernel

theorem rows11355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11355 = true := by
  decide +kernel

theorem tot11355 : totK PD2M8K2 D2M8K2.t11355 = [0, 174485292691, 446833501781, 251545831259, 22828318141, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
