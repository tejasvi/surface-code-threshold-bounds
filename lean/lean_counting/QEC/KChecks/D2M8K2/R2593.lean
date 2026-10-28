import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10372 = true := by
  decide +kernel

theorem tot10372 : totK PD2M8K2 D2M8K2.t10372 = [0, 0, 0, 290355525942, 501103464411, 96307459781, 1369150432, 0] := by
  decide +kernel

theorem rows10373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10373 = true := by
  decide +kernel

theorem tot10373 : totK PD2M8K2 D2M8K2.t10373 = [0, 0, 86643100371, 382664495624, 389580985224, 42371750144, 0, 0] := by
  decide +kernel

theorem rows10374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10374 = true := by
  decide +kernel

theorem tot10374 : totK PD2M8K2 D2M8K2.t10374 = [0, 0, 200125263309, 481602256083, 180038014895, 4983999782, 0, 0] := by
  decide +kernel

theorem rows10375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10375 = true := by
  decide +kernel

theorem tot10375 : totK PD2M8K2 D2M8K2.t10375 = [0, 0, 33514940640, 341239691322, 436074595632, 56075637837, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
