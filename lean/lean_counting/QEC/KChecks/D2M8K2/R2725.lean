import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10900 = true := by
  decide +kernel

theorem tot10900 : totK PD2M8K2 D2M8K2.t10900 = [0, 0, 159950037561, 455809851951, 268617925792, 21958861232, 0, 0] := by
  decide +kernel

theorem rows10901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10901 = true := by
  decide +kernel

theorem tot10901 : totK PD2M8K2 D2M8K2.t10901 = [0, 0, 181688270574, 470609635640, 246611571064, 15079379989, 0, 0] := by
  decide +kernel

theorem rows10902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10902 = true := by
  decide +kernel

theorem tot10902 : totK PD2M8K2 D2M8K2.t10902 = [0, 174434339562, 426077475608, 213430740267, 63034710071, 9758758476, 0, 0] := by
  decide +kernel

theorem rows10903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10903 = true := by
  decide +kernel

theorem tot10903 : totK PD2M8K2 D2M8K2.t10903 = [0, 195117940401, 461245065618, 213175313051, 12489778283, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
