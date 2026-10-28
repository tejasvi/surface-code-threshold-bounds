import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11664 = true := by
  decide +kernel

theorem tot11664 : totK PD2M8K2 D2M8K2.t11664 = [0, 170308802673, 413096381337, 245228343152, 49095907736, 2561774784, 0, 0] := by
  decide +kernel

theorem rows11665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11665 = true := by
  decide +kernel

theorem tot11665 : totK PD2M8K2 D2M8K2.t11665 = [0, 199265566118, 469089120355, 223192485834, 12762375291, 0, 0, 0] := by
  decide +kernel

theorem rows11666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11666 = true := by
  decide +kernel

theorem tot11666 : totK PD2M8K2 D2M8K2.t11666 = [159499817693, 355717787715, 245954512359, 125594414065, 13462490481, 0, 0, 0] := by
  decide +kernel

theorem rows11667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11667 = true := by
  decide +kernel

theorem tot11667 : totK PD2M8K2 D2M8K2.t11667 = [182118286906, 456602072785, 232479111397, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
