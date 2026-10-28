import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4252 = true := by
  decide +kernel

theorem tot4252 : totK PD2M8K2 D2M8K2.t4252 = [0, 0, 0, 306031486413, 526412142320, 87009134105, 0, 0] := by
  decide +kernel

theorem rows4253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4253 = true := by
  decide +kernel

theorem tot4253 : totK PD2M8K2 D2M8K2.t4253 = [0, 0, 165327025006, 387654334851, 258151284259, 85762723260, 2586295899, 0] := by
  decide +kernel

theorem rows4254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4254 = true := by
  decide +kernel

theorem tot4254 : totK PD2M8K2 D2M8K2.t4254 = [0, 0, 157939250589, 451784552972, 279873266285, 21648241694, 0, 0] := by
  decide +kernel

theorem rows4255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4255 = true := by
  decide +kernel

theorem tot4255 : totK PD2M8K2 D2M8K2.t4255 = [0, 0, 92327302135, 352704171612, 383137953278, 70504184005, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
