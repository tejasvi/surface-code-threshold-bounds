import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1320 = true := by
  decide +kernel

theorem tot1320 : totK PD2M8K2 D2M8K2.t1320 = [0, 173339279093, 440504508908, 254258814439, 25119899710, 0, 0, 0] := by
  decide +kernel

theorem rows1321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1321 = true := by
  decide +kernel

theorem tot1321 : totK PD2M8K2 D2M8K2.t1321 = [0, 191948459449, 496372083955, 201882730759, 5081207699, 0, 0, 0] := by
  decide +kernel

theorem rows1322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1322 = true := by
  decide +kernel

theorem tot1322 : totK PD2M8K2 D2M8K2.t1322 = [171313231716, 421651929242, 234156771584, 62995618383, 5618966238, 0, 0, 0] := by
  decide +kernel

theorem rows1323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1323 = true := by
  decide +kernel

theorem tot1323 : totK PD2M8K2 D2M8K2.t1323 = [187313458747, 453988990865, 231825668932, 17914461613, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
