import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3188 = true := by
  decide +kernel

theorem tot3188 : totK PD2M8K2 D2M8K2.t3188 = [0, 0, 307956756887, 466589382221, 81744858804, 1239866073, 0, 0] := by
  decide +kernel

theorem rows3189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3189 = true := by
  decide +kernel

theorem tot3189 : totK PD2M8K2 D2M8K2.t3189 = [0, 93173791751, 394887475165, 373556101360, 41583012526, 0, 0, 0] := by
  decide +kernel

theorem rows3190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3190 = true := by
  decide +kernel

theorem tot3190 : totK PD2M8K2 D2M8K2.t3190 = [0, 191305922846, 466743894105, 244909674844, 18389446352, 0, 0, 0] := by
  decide +kernel

theorem rows3191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3191 = true := by
  decide +kernel

theorem tot3191 : totK PD2M8K2 D2M8K2.t3191 = [0, 190918818897, 472996637936, 220790763637, 14338664516, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
