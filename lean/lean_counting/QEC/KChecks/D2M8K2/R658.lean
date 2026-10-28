import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2632 = true := by
  decide +kernel

theorem tot2632 : totK PD2M8K2 D2M8K2.t2632 = [0, 0, 193738006738, 474184044881, 192555659324, 8824320960, 0, 0] := by
  decide +kernel

theorem rows2633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2633 = true := by
  decide +kernel

theorem tot2633 : totK PD2M8K2 D2M8K2.t2633 = [0, 168997499532, 443158041374, 276185988812, 34085109727, 0, 0, 0] := by
  decide +kernel

theorem rows2634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2634 = true := by
  decide +kernel

theorem tot2634 : totK PD2M8K2 D2M8K2.t2634 = [0, 181605115423, 463791104997, 232265656568, 17012752274, 0, 0, 0] := by
  decide +kernel

theorem rows2635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2635 = true := by
  decide +kernel

theorem tot2635 : totK PD2M8K2 D2M8K2.t2635 = [0, 66882214126, 363432923541, 403485719078, 66995814990, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
