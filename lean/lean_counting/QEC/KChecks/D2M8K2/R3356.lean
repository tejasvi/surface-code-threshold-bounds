import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13424 = true := by
  decide +kernel

theorem tot13424 : totK PD2M8K2 D2M8K2.t13424 = [0, 0, 111594056885, 451103244171, 315913987730, 30343206364, 0, 0] := by
  decide +kernel

theorem rows13425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13425 = true := by
  decide +kernel

theorem tot13425 : totK PD2M8K2 D2M8K2.t13425 = [0, 0, 0, 216330067101, 495901853568, 149562093254, 9751947372, 0] := by
  decide +kernel

theorem rows13426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13426 = true := by
  decide +kernel

theorem tot13426 : totK PD2M8K2 D2M8K2.t13426 = [0, 0, 156794657063, 454871093920, 284166381324, 26221493628, 0, 0] := by
  decide +kernel

theorem rows13427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13427 = true := by
  decide +kernel

theorem tot13427 : totK PD2M8K2 D2M8K2.t13427 = [0, 0, 189381107087, 466750923149, 225077777617, 12459280195, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
