import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10692 = true := by
  decide +kernel

theorem tot10692 : totK PD2M8K2 D2M8K2.t10692 = [0, 0, 172214411719, 472921818188, 260440810299, 14897633287, 0, 0] := by
  decide +kernel

theorem rows10693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10693 = true := by
  decide +kernel

theorem tot10693 : totK PD2M8K2 D2M8K2.t10693 = [0, 0, 0, 244138062634, 497910024228, 174970088673, 9977052014, 0] := by
  decide +kernel

theorem rows10694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10694 = true := by
  decide +kernel

theorem tot10694 : totK PD2M8K2 D2M8K2.t10694 = [0, 0, 90154250814, 291294295732, 372575112057, 144320784279, 5430665091, 0] := by
  decide +kernel

theorem rows10695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10695 = true := by
  decide +kernel

theorem tot10695 : totK PD2M8K2 D2M8K2.t10695 = [0, 0, 174038076163, 447113611153, 263844804451, 30484327524, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
