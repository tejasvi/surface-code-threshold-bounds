import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8208 = true := by
  decide +kernel

theorem tot8208 : totK PD2M8K2 D2M8K2.t8208 = [0, 0, 0, 249601947782, 473783721644, 135916004144, 4879840392, 0] := by
  decide +kernel

theorem rows8209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8209 = true := by
  decide +kernel

theorem tot8209 : totK PD2M8K2 D2M8K2.t8209 = [0, 0, 169984932980, 435429409064, 260160561816, 26588136150, 0, 0] := by
  decide +kernel

theorem rows8210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8210 = true := by
  decide +kernel

theorem tot8210 : totK PD2M8K2 D2M8K2.t8210 = [0, 0, 141545603510, 434753699149, 288122096333, 25621669488, 0, 0] := by
  decide +kernel

theorem rows8211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8211 = true := by
  decide +kernel

theorem tot8211 : totK PD2M8K2 D2M8K2.t8211 = [0, 0, 89503525964, 354327934385, 370126702936, 66258386010, 1107157161, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
