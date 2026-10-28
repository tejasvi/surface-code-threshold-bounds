import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3168 = true := by
  decide +kernel

theorem tot3168 : totK PD2M8K2 D2M8K2.t3168 = [74462343477, 359995927721, 427128864948, 54214272149, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3169 = true := by
  decide +kernel

theorem tot3169 : totK PD2M8K2 D2M8K2.t3169 = [178154226101, 459432307261, 267072484509, 27957473184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3170 = true := by
  decide +kernel

theorem tot3170 : totK PD2M8K2 D2M8K2.t3170 = [174351684497, 474711099698, 246509534522, 13672237646, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3171 = true := by
  decide +kernel

theorem tot3171 : totK PD2M8K2 D2M8K2.t3171 = [0, 219915269671, 459839017886, 215696968429, 21379198785, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
