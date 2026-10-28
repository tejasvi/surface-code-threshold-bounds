import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1352 = true := by
  decide +kernel

theorem tot1352 : totK PD2M8K2 D2M8K2.t1352 = [0, 18947402031, 195428148026, 433950966282, 210748290127, 16939352947, 0, 0] := by
  decide +kernel

theorem rows1353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1353 = true := by
  decide +kernel

theorem tot1353 : totK PD2M8K2 D2M8K2.t1353 = [0, 199868569105, 486484533400, 208208434489, 9778478082, 0, 0, 0] := by
  decide +kernel

theorem rows1354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1354 = true := by
  decide +kernel

theorem tot1354 : totK PD2M8K2 D2M8K2.t1354 = [0, 199259443145, 471108894579, 210591562449, 12414379003, 0, 0, 0] := by
  decide +kernel

theorem rows1355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1355 = true := by
  decide +kernel

theorem tot1355 : totK PD2M8K2 D2M8K2.t1355 = [0, 19434252169, 308992804023, 472094842450, 100068679898, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
