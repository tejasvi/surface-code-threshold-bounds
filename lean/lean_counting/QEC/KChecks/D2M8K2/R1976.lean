import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7904 = true := by
  decide +kernel

theorem tot7904 : totK PD2M8K2 D2M8K2.t7904 = [0, 0, 163420171213, 466745283608, 250530173991, 15158935776, 0, 0] := by
  decide +kernel

theorem rows7905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7905 = true := by
  decide +kernel

theorem tot7905 : totK PD2M8K2 D2M8K2.t7905 = [0, 0, 197454689954, 476521758216, 203561685847, 11071105621, 0, 0] := by
  decide +kernel

theorem rows7906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7906 = true := by
  decide +kernel

theorem tot7906 : totK PD2M8K2 D2M8K2.t7906 = [0, 0, 200553864827, 470658739001, 205855181380, 12096313584, 0, 0] := by
  decide +kernel

theorem rows7907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7907 = true := by
  decide +kernel

theorem tot7907 : totK PD2M8K2 D2M8K2.t7907 = [0, 0, 11526037961, 348455662726, 420553329975, 64857293104, 1053411165, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
