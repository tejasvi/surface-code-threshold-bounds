import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3976 = true := by
  decide +kernel

theorem tot3976 : totK PD2M8K2 D2M8K2.t3976 = [0, 0, 180336160463, 474339297149, 232113992497, 11577031045, 0, 0] := by
  decide +kernel

theorem rows3977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3977 = true := by
  decide +kernel

theorem tot3977 : totK PD2M8K2 D2M8K2.t3977 = [0, 173861880260, 398985633423, 214373199147, 92500038497, 12306475495, 0, 0] := by
  decide +kernel

theorem rows3978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3978 = true := by
  decide +kernel

theorem tot3978 : totK PD2M8K2 D2M8K2.t3978 = [0, 182868867752, 451909539969, 222684208709, 12975004289, 0, 0, 0] := by
  decide +kernel

theorem rows3979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3979 = true := by
  decide +kernel

theorem tot3979 : totK PD2M8K2 D2M8K2.t3979 = [0, 37663951278, 321937412423, 434979178405, 90808663829, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
