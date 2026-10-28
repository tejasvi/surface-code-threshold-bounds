import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9248 = true := by
  decide +kernel

theorem tot9248 : totK PD2M8K2 D2M8K2.t9248 = [0, 0, 198424149802, 455591505265, 185459424180, 11853261585, 0, 0] := by
  decide +kernel

theorem rows9249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9249 = true := by
  decide +kernel

theorem tot9249 : totK PD2M8K2 D2M8K2.t9249 = [0, 170315919782, 458296182841, 248759739338, 19447131356, 0, 0, 0] := by
  decide +kernel

theorem rows9250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9250 = true := by
  decide +kernel

theorem tot9250 : totK PD2M8K2 D2M8K2.t9250 = [0, 195687126691, 469215510867, 217444422877, 13468795916, 0, 0, 0] := by
  decide +kernel

theorem rows9251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9251 = true := by
  decide +kernel

theorem tot9251 : totK PD2M8K2 D2M8K2.t9251 = [0, 54931279854, 357376018087, 382100729258, 59409648346, 1021600638, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
