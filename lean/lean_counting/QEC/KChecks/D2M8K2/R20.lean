import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows80 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t80 = true := by
  decide +kernel

theorem tot80 : totK PD2M8K2 D2M8K2.t80 = [162822319824, 437759744274, 260411005779, 38287932091, 0, 0, 0, 0] := by
  decide +kernel

theorem rows81 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t81 = true := by
  decide +kernel

theorem tot81 : totK PD2M8K2 D2M8K2.t81 = [162905160969, 430792985320, 280306848624, 24632991169, 0, 0, 0, 0] := by
  decide +kernel

theorem rows82 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t82 = true := by
  decide +kernel

theorem tot82 : totK PD2M8K2 D2M8K2.t82 = [83535095516, 359077238518, 363384806064, 73142431032, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows83 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t83 = true := by
  decide +kernel

theorem tot83 : totK PD2M8K2 D2M8K2.t83 = [0, 272267923505, 518052983434, 111362198572, 1069412848, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
